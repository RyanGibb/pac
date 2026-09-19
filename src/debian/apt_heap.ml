type kind = Forced | Package | Hard | Soft | Alternative

module type DRIVER = sig
  type name
  type version
  type atom
  type assigned

  val pp_name : Format.formatter -> name -> unit
  val pp_atom : Format.formatter -> atom -> unit
  val kind : name -> kind
  val clause_atoms : name -> atom list option
  val atom_count : assigned -> atom -> int
  val atom_static : atom -> int
  val decided : assigned -> name -> version option
  val version_equal : version -> version -> bool
  val wave : name -> version -> (bool * name option * atom list) list
  val continuation : name -> version -> name option
  val fallback_key : name -> int * int
end

module Make (D : DRIVER) = struct
  (* A work item of apt's Solver::Work (solver3.cc): size is the live
     solution count frozen at push, nsol the clause's static solution count,
     level the wide-decision depth at push.  eager is not carried because it
     is [not wopt]: the Clause constructor (solver3.h) sets eager(not
     optional), so every hard clause outranks every Recommends. *)
  type witem = {
    wname : D.name;
    wopt : bool;
    wsize : int;
    wnsol : int;
    wlevel : int;
  }

  (* Our own decision trail, to detect PubGrub's backjumps by diffing the
     partial solution: a fallen suffix is apt's Pop, level by level. *)
  type tentry = {
    tname : D.name;
    mutable tval : D.version option;
    twide : bool;
    tlevel : int;
  }

  type t = {
    seen : (D.name, int) Hashtbl.t;
    mutable clock : int;
    mutable harr : witem array;
    mutable hlen : int;
    mutable tarr : tentry array;
    mutable tlen : int;
    (* the wide-decision depth, apt's decision level *)
    mutable wide_count : int;
    (* trail entries whose propagation wave has already been pushed *)
    mutable waved_upto : int;
    popped_at : (int, witem list ref) Hashtbl.t;
    (* Selectors opened by deciding a clause gadget to one of its
       alternatives: apt chose a concrete solution at that pop or enqueue, so
       the selector is the pending half of the same step and is decided
       before the heap moves on. *)
    conts : (D.name, unit) Hashtbl.t;
    nsol_tbl : (D.name, int) Hashtbl.t;
    mutable c_t0 : int;
    mutable c_sel : int;
    mutable c_pop : int;
    mutable c_elide : int;
    mutable c_desync : int;
    mutable c_fb : int;
    mutable c_push : int;
    mutable c_readd : int;
    mutable c_unwind : int;
  }

  let create () =
    {
      seen = Hashtbl.create 4096;
      clock = 0;
      harr = [||];
      hlen = 0;
      tarr = [||];
      tlen = 0;
      wide_count = 0;
      waved_upto = 0;
      popped_at = Hashtbl.create 64;
      conts = Hashtbl.create 64;
      nsol_tbl = Hashtbl.create 1024;
      c_t0 = 0;
      c_sel = 0;
      c_pop = 0;
      c_elide = 0;
      c_desync = 0;
      c_fb = 0;
      c_push = 0;
      c_readd = 0;
      c_unwind = 0;
    }

  let discover t n =
    if not (Hashtbl.mem t.seen n) then (
      t.clock <- t.clock + 1;
      Hashtbl.add t.seen n t.clock)

  let discovered t n = try Hashtbl.find t.seen n with Not_found -> max_int
  let shadow_dbg = Sys.getenv_opt "PACSHADOWDBG" <> None

  let dbg fmt =
    if shadow_dbg then Format.eprintf fmt
    else Format.ifprintf Format.err_formatter fmt

  (* Work::operator< (solver3.cc:60): a is less important than b *)
  let wless a b =
    let ua = (not a.wopt) && a.wsize < 2 and ub = (not b.wopt) && b.wsize < 2 in
    if ua <> ub then ub
    else if a.wopt <> b.wopt then a.wopt (* eager = not optional *)
    else if a.wsize < 2 <> (b.wsize < 2) then b.wsize < 2
    else if a.wsize = 1 && b.wsize = 1 then a.wnsol < b.wnsol
    else false

  (* The heap itself reproduces libstdc++'s __push_heap/__adjust_heap
     exactly, because ties in Work::operator< are settled by nothing
     else. *)

  (* libstdc++ __push_heap *)
  let sift_up t hole top value =
    let a = t.harr in
    let hole = ref hole in
    let brk = ref false in
    while not !brk do
      let parent = (!hole - 1) / 2 in
      if !hole > top && wless a.(parent) value then (
        a.(!hole) <- a.(parent);
        hole := parent)
      else brk := true
    done;
    a.(!hole) <- value

  (* libstdc++ __adjust_heap: the hole walks to a leaf along the greater
     child -- the right one when they tie -- and the displaced value is then
     sifted back up.  Ties travel differently than under a textbook
     sift-down, which is precisely what is being reproduced. *)
  let adjust t hole len value =
    let a = t.harr in
    let top = hole in
    let hole = ref hole in
    let second = ref top in
    while !second < (len - 1) / 2 do
      second := 2 * (!second + 1);
      if wless a.(!second) a.(!second - 1) then decr second;
      a.(!hole) <- a.(!second);
      hole := !second
    done;
    if len land 1 = 0 && !second = (len - 2) / 2 then (
      second := 2 * (!second + 1);
      a.(!hole) <- a.(!second - 1);
      hole := !second - 1);
    sift_up t !hole top value

  let hpush t w =
    if t.hlen = Array.length t.harr then (
      let na = Array.make (max 256 (2 * t.hlen)) w in
      Array.blit t.harr 0 na 0 t.hlen;
      t.harr <- na);
    t.harr.(t.hlen) <- w;
    t.hlen <- t.hlen + 1;
    sift_up t (t.hlen - 1) 0 w

  let hpop t =
    let a = t.harr in
    let front = a.(0) in
    if t.hlen > 1 then (
      let value = a.(t.hlen - 1) in
      a.(t.hlen - 1) <- a.(0);
      adjust t 0 (t.hlen - 1) value);
    t.hlen <- t.hlen - 1;
    front

  let hmake t =
    let len = t.hlen in
    if len >= 2 then
      let parent = ref ((len - 2) / 2) in
      let brk = ref false in
      while not !brk do
        adjust t !parent len t.harr.(!parent);
        if !parent = 0 then brk := true else decr parent
      done

  (* Solver::Pop erases with std::remove_if (stable) then re-heapifies *)
  let herase t keep =
    let a = t.harr in
    let j = ref 0 in
    for i = 0 to t.hlen - 1 do
      if keep a.(i) then (
        a.(!j) <- a.(i);
        incr j)
    done;
    t.hlen <- !j;
    hmake t

  let static_nsol_atoms atoms =
    List.fold_left (fun acc a -> acc + D.atom_static a) 0 atoms

  let static_nsol t n =
    match Hashtbl.find_opt t.nsol_tbl n with
    | Some k -> k
    | None ->
        let k =
          match D.clause_atoms n with
          | Some atoms -> static_nsol_atoms atoms
          | None -> max_int
        in
        Hashtbl.add t.nsol_tbl n k;
        k

  let live_size ~assigned atoms =
    (* only < 2 and = 1 matter to the comparator, so cap the count *)
    let rec go acc = function
      | [] -> acc
      | _ when acc >= 2 -> acc
      | a :: rest -> go (acc + D.atom_count assigned a) rest
    in
    go 0 atoms

  let live_of_name ~assigned n =
    match D.clause_atoms n with
    | Some atoms -> live_size ~assigned atoms
    | None -> 0

  let tpush t e =
    if t.tlen = Array.length t.tarr then (
      let na = Array.make (max 256 (2 * t.tlen)) e in
      Array.blit t.tarr 0 na 0 t.tlen;
      t.tarr <- na);
    t.tarr.(t.tlen) <- e;
    t.tlen <- t.tlen + 1

  let record_popped t lvl w =
    match Hashtbl.find_opt t.popped_at lvl with
    | Some r -> r := w :: !r
    | None -> Hashtbl.add t.popped_at lvl (ref [ w ])

  let standing t ~assigned (e : tentry) =
    match D.decided assigned e.tname with
    | None -> false
    | Some pv -> (
        match e.tval with
        | Some pv' -> D.version_equal pv pv'
        | None ->
            e.tval <- Some pv;
            (match D.continuation e.tname pv with
            | Some c -> Hashtbl.replace t.conts c ()
            | None -> ());
            true)

  (* Solver::Pop for one level: UndoOne re-AddWorks the level's popped items
     newest first (recounting size; a statically-unit hard clause is
     enqueued, i.e. left to tier 0), then items above the level are erased
     and the heap rebuilt. *)
  let unwind_level t ~assigned lvl =
    t.c_unwind <- t.c_unwind + 1;
    (match Hashtbl.find_opt t.popped_at lvl with
    | Some r ->
        List.iter
          (fun (w : witem) ->
            if w.wopt || w.wnsol > 1 then (
              t.c_readd <- t.c_readd + 1;
              hpush t { w with wsize = live_of_name ~assigned w.wname }))
          !r;
        Hashtbl.remove t.popped_at lvl
    | None -> ());
    herase t (fun w -> w.wlevel <= lvl - 1)

  let sync t ~assigned =
    let cut = ref t.tlen in
    let brk = ref false in
    while (not !brk) && !cut > 0 do
      if standing t ~assigned t.tarr.(!cut - 1) then brk := true else decr cut
    done;
    if !cut < t.tlen then (
      for i = t.tlen - 1 downto !cut do
        let e = t.tarr.(i) in
        if e.twide then (
          unwind_level t ~assigned e.tlevel;
          t.wide_count <- t.wide_count - 1)
      done;
      t.tlen <- !cut;
      if t.waved_upto > t.tlen then t.waved_upto <- t.tlen)

  (* the propagation wave of each standing decision: a decided package's
     clauses are pushed in field order; a statically-unit hard clause is
     apt's Enqueue and never becomes a work item *)
  let wave t ~assigned =
    for i = t.waved_upto to t.tlen - 1 do
      let e = t.tarr.(i) in
      match e.tval with
      | None -> ()
      | Some pv ->
          List.iter
            (fun (opt, g, atoms) ->
              match g with
              | None -> ()
              | Some g ->
                  let nsol = static_nsol_atoms atoms in
                  Hashtbl.replace t.nsol_tbl g nsol;
                  if opt || nsol > 1 then (
                    t.c_push <- t.c_push + 1;
                    let sz = live_size ~assigned atoms in
                    dbg "PUSH (%d/%d@%d)%s %a@." sz nsol e.tlevel
                      (if opt then " opt" else "")
                      D.pp_name g;
                    hpush t
                      {
                        wname = g;
                        wopt = opt;
                        wsize = sz;
                        wnsol = nsol;
                        wlevel = e.tlevel;
                      }))
            (D.wave e.tname pv)
    done;
    t.waved_upto <- t.tlen

  (* the key the traversal used before the heap, kept as the fallback for
     when the heap has no item to offer (the goal itself, and any desync) *)
  let oldpick t open_names =
    let key (n, count) =
      let optional = D.kind n = Soft in
      let group, total = D.fallback_key n in
      ( (if (not optional) && count < 2 then 0 else 1),
        group,
        (if count < 2 then 0 else 1),
        total,
        discovered t n )
    in
    match open_names with
    | [] -> invalid_arg "next"
    | e :: es ->
        fst
          (List.fold_left
             (fun acc e -> if compare (key e) (key acc) < 0 then e else acc)
             e es)

  let next t ~assigned open_names =
    sync t ~assigned;
    wave t ~assigned;
    let offered = Hashtbl.create 64 in
    List.iter (fun (n, c) -> Hashtbl.replace offered n c) open_names;
    let ret ~wide n =
      let lvl =
        if wide then (
          t.wide_count <- t.wide_count + 1;
          t.wide_count)
        else t.wide_count
      in
      tpush t { tname = n; tval = None; twide = wide; tlevel = lvl };
      n
    in
    (* tier 0: apt's Enqueues -- negative clauses, forced names, and hard
       clauses down to one live solution -- drained in discovery order as a
       stand-in for the propagation queue *)
    let t0 =
      List.fold_left
        (fun acc (n, c) ->
          let is0 =
            match D.kind n with
            | Forced -> true
            | Soft -> false
            | Hard ->
                static_nsol t n <= 1 || (c < 2 && live_of_name ~assigned n <= 1)
            | Alternative ->
                (* one live target package is apt's Enqueue whatever the
                   version count -- the choice left is only which version,
                   which apt defers but resolves identically *)
                c < 2 || live_of_name ~assigned n <= 1
            | Package ->
                (* a package brought in is apt's Enqueue of its var; the
                   version pick apt defers to a SelectVersion item lands on
                   the same newest candidate either way *)
                true
          in
          if not is0 then acc
          else
            match acc with
            | Some (_, d) when d <= discovered t n -> acc
            | _ -> Some (n, discovered t n))
        None open_names
    in
    match t0 with
    | Some (n, _) ->
        t.c_t0 <- t.c_t0 + 1;
        ret ~wide:false n
    | None -> (
        (* the selector opened by a clause decision: apt chose a concrete
           solution at that pop, this finishes the same choice *)
        let sel =
          List.fold_left
            (fun acc (n, _) ->
              if D.kind n = Alternative && Hashtbl.mem t.conts n then
                match acc with
                | Some (_, d) when d <= discovered t n -> acc
                | _ -> Some (n, discovered t n)
              else acc)
            None open_names
        in
        match sel with
        | Some (n, _) ->
            t.c_sel <- t.c_sel + 1;
            Hashtbl.remove t.conts n;
            ret ~wide:false n
        | None -> (
            let rec pop () =
              if t.hlen = 0 then None
              else
                let w = hpop t in
                let watoms fmt w =
                  match D.clause_atoms w.wname with
                  | Some atoms ->
                      Format.pp_print_list
                        ~pp_sep:(fun fmt () -> Format.fprintf fmt " | ")
                        D.pp_atom fmt atoms
                  | None -> D.pp_name fmt w.wname
                in
                if Hashtbl.mem offered w.wname then (
                  t.c_pop <- t.c_pop + 1;
                  dbg "POP (%d/%d@%d) %a [%a]@." w.wsize w.wnsol w.wlevel
                    D.pp_name w.wname watoms w;
                  let r = ret ~wide:true w.wname in
                  record_popped t t.wide_count w;
                  Some r)
                else (
                  (match D.decided assigned w.wname with
                  | Some _ ->
                      t.c_elide <- t.c_elide + 1;
                      dbg "ELIDE (%d/%d@%d) %a@." w.wsize w.wnsol w.wlevel
                        D.pp_name w.wname
                  | None ->
                      t.c_desync <- t.c_desync + 1;
                      dbg "DESYNC (%d/%d@%d) %a@." w.wsize w.wnsol w.wlevel
                        D.pp_name w.wname);
                  record_popped t t.wide_count w;
                  pop ())
            in
            match pop () with
            | Some n -> n
            | None ->
                t.c_fb <- t.c_fb + 1;
                let n = oldpick t open_names in
                dbg "FALLBACK %a (open %d)@." D.pp_name n
                  (List.length open_names);
                ret ~wide:true n))

  let report t =
    if Sys.getenv_opt "PACSHADOW" <> None then
      Printf.eprintf
        "PACSHADOW tier0=%d selstep=%d pop=%d elide=%d desync=%d fallback=%d \
         push=%d readd=%d unwind=%d\n\
         %!"
        t.c_t0 t.c_sel t.c_pop t.c_elide t.c_desync t.c_fb t.c_push t.c_readd
        t.c_unwind
end
