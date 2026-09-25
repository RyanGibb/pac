type kind = Package | Hard | Soft | Alternative

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
  val obsolete : atom -> bool
  val decided : assigned -> name -> version option
  val satisfied : assigned -> name -> bool

  type rejection

  val pp_rejection : Format.formatter -> rejection -> unit
  val conflicts : assigned -> name -> version -> rejection list
  val conflicted_by : assigned -> name -> version -> rejection list
  val propagate : assigned -> rejection -> rejection list * name list
  val reset : unit -> unit
  val version_equal : version -> version -> bool

  val wave :
    name ->
    version ->
    (bool * name option * atom list) list
    * (bool * name option * atom list) list

  val continuation : name -> version -> name list
  val forced_to : name -> version -> name option
  val version_of : name -> version -> (name * version) option
  val head : assigned -> atom list -> (name * (name * version) option) option
  val same_name : name -> name -> bool
  val negation : assigned -> name -> version -> rejection list
  val assign : assigned -> rejection list -> rejection list
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
    (* the clause's group is SatisfyObsolete rather than SatisfyNew, as from
       an empty system every other clause's is (solver3.cc:1103-1107) *)
    wobs : bool;
    (* the alternatives the item's solutions are counted over, as the wave
       that pushed it read them: narrower than the name's own where apt
       folded a second clause on the same target into this one *)
    watoms : D.atom list;
  }

  (* Our own decision trail, to detect PubGrub's backjumps by diffing the
     partial solution: a fallen suffix is apt's Pop, level by level. *)
  type tentry = {
    tname : D.name;
    mutable tval : D.version option;
    twide : bool;
    tlevel : int;
    (* its place in the trail, which a fallen suffix is cut from *)
    tidx : int;
    (* the names this decision's wave enqueued: apt unassigns them with the
       decision, and re-enqueues afresh whatever a later wave requires *)
    mutable tenq : D.name list;
    (* the packages whose version var popped with this decision *)
    mutable tvd : D.name list;
    (* undone by PubGrub's backjump but standing for apt, whose Pop undoes
       one level: to be decided again, to the same version, before the
       search moves on *)
    mutable tredo : bool;
  }

  type entry =
    | Reject of D.rejection
    | VerOf of tentry * D.version * (bool * D.name option * D.atom list) list
    (* a version var apt enqueued as a clause's one solution: its pop queues
       the package var and walks the version's clauses *)
    | VerFirst of tentry * D.name * D.version

  type t = {
    (* apt's propagation queue (propQ, solver3.cc) as the slot each name was
       enqueued at: a wave's unit clauses append their solution in field
       order, behind everything queued before, and the tier-0 drain takes
       the smallest slot.  A name is queued only when apt would Enqueue it,
       so an alternative of a wide clause has no slot until that clause is
       decided to it. *)
    pos : (D.name, int) Hashtbl.t;
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
    (* packages whose version var has popped -- reached through a selector,
       so the version came first and the package var joined the queue behind
       -- and whose own pop therefore owes no version entry *)
    ver_done : (D.name, unit) Hashtbl.t;
    (* packages whose version var is queued ahead of them: their package var
       gets its slot as that entry pops, not before *)
    pending : (D.name, unit) Hashtbl.t;
    (* the versions the trail's redo entries are to be decided at again *)
    keep : (D.name, D.version) Hashtbl.t;
    (* apt re-examines a clause only when a literal it watches changes; the
       drain's unit test of an open name is likewise kept from one call to
       the next while nothing it depends on has: PubGrub's own count of the
       name's candidates, which its propagation narrows as a target is
       decided or excluded, and the rejections propagated so far *)
    nonunit : (D.name, int * int) Hashtbl.t;
    mutable epoch : int;
    mutable nredo : int;
    (* the negations Pop asserted, each at the level it was asserted at,
       newest first: apt keeps one while that level stands, through any
       later Pop above it, while a replay derives rejections afresh from the
       standing decisions alone *)
    mutable negations : (int * D.rejection list) list;
    nsol_tbl : (D.name, int) Hashtbl.t;
    (* the alternatives the last wave to queue or push a name counted it
       over, for the unit test the queue drain makes of it *)
    atoms_tbl : (D.name, D.atom list) Hashtbl.t;
    (* the entries of apt's queue that are not a name to decide, each at its
       slot, taken when the drain reaches it, ahead of every name queued
       after it and after every one queued before: a rejection to propagate,
       or a decided package's version var, whose pop walks the clauses
       registered on it and assigns what conflicts with it *)
    rq : (int * entry) Queue.t;
    mutable c_t0 : int;
    mutable c_prop : int;
    mutable c_pop : int;
    mutable c_elide : int;
    mutable c_drop : int;
    mutable c_desync : int;
    mutable c_push : int;
    mutable c_readd : int;
    mutable c_unwind : int;
    (* PubGrub backjumps seen, whether or not a level fell with them *)
    mutable c_fall : int;
  }

  let create () =
    {
      pos = Hashtbl.create 4096;
      clock = 0;
      harr = [||];
      hlen = 0;
      tarr = [||];
      tlen = 0;
      wide_count = 0;
      waved_upto = 0;
      popped_at = Hashtbl.create 64;
      ver_done = Hashtbl.create 64;
      pending = Hashtbl.create 64;
      keep = Hashtbl.create 64;
      nonunit = Hashtbl.create 4096;
      epoch = 0;
      nredo = 0;
      negations = [];
      nsol_tbl = Hashtbl.create 1024;
      atoms_tbl = Hashtbl.create 1024;
      rq = Queue.create ();
      c_t0 = 0;
      c_prop = 0;
      c_pop = 0;
      c_elide = 0;
      c_drop = 0;
      c_desync = 0;
      c_push = 0;
      c_readd = 0;
      c_unwind = 0;
      c_fall = 0;
    }

  let shadow_dbg = Sys.getenv_opt "PACSHADOWDBG" <> None

  let dbg fmt =
    if shadow_dbg then Format.eprintf fmt
    else Format.ifprintf Format.err_formatter fmt

  let watoms fmt n =
    match D.clause_atoms n with
    | Some atoms ->
        Format.pp_print_list
          ~pp_sep:(fun fmt () -> Format.fprintf fmt " | ")
          D.pp_atom fmt atoms
    | None -> D.pp_name fmt n

  let pp_reason fmt = function
    | Some (e : tentry) -> D.pp_name fmt e.tname
    | None -> Format.pp_print_string fmt "-"

  (* apt's Enqueue, attributed to the decision whose wave made it *)
  let enqueue t (e : tentry option) n =
    if not (Hashtbl.mem t.pos n) then (
      t.clock <- t.clock + 1;
      Hashtbl.add t.pos n t.clock;
      dbg "ENQ #%d %a -> %a [%a]@." t.clock pp_reason e D.pp_name n watoms n;
      match e with Some e -> e.tenq <- n :: e.tenq | None -> ())

  let queue_rejections t rs =
    List.iter
      (fun r ->
        t.clock <- t.clock + 1;
        dbg "RQ #%d %a@." t.clock D.pp_rejection r;
        Queue.add (t.clock, Reject r) t.rq)
      rs

  (* Work::operator< (solver3.cc:60): a is less important than b *)
  let wless a b =
    let ua = (not a.wopt) && a.wsize < 2 and ub = (not b.wopt) && b.wsize < 2 in
    if ua <> ub then ub
    else if a.wopt <> b.wopt then a.wopt (* eager = not optional *)
    else if a.wobs <> b.wobs then a.wobs
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

  let live_of_name t ~assigned n =
    match Hashtbl.find_opt t.atoms_tbl n with
    | Some atoms -> live_size ~assigned atoms
    | None -> (
        match D.clause_atoms n with
        | Some atoms -> live_size ~assigned atoms
        | None -> 0)

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
    | None -> e.tredo
    | Some pv -> (
        match e.tval with
        | Some pv' ->
            let same = D.version_equal pv pv' in
            if same && e.tredo then (
              e.tredo <- false;
              t.nredo <- t.nredo - 1;
              Hashtbl.remove t.keep e.tname);
            same
        | None ->
            e.tval <- Some pv;
            true)

  let kept t n = Hashtbl.find_opt t.keep n

  (* one clause of a decided package as Solver::Propagate meets it: a hard
     clause down to one live solution is apt's Enqueue and takes the next
     queue slot, any other live clause is a work item, and an optional clause
     nothing can satisfy any more is dropped *)
  let clause t ~assigned (e : tentry) (opt, g, atoms) =
    match g with
    | None -> ()
    | Some g -> (
        let nsol = static_nsol_atoms atoms in
        Hashtbl.replace t.nsol_tbl g nsol;
        Hashtbl.replace t.atoms_tbl g atoms;
        let sz = live_size ~assigned atoms in
        if (opt && sz >= 1) || sz >= 2 then (
          t.c_push <- t.c_push + 1;
          dbg "PUSH (%d/%d@%d)%s %a -> %a [%a]@." sz nsol e.tlevel
            (if opt then " opt" else "")
            D.pp_name e.tname D.pp_name g watoms g;
          hpush t
            {
              wname = g;
              wopt = opt;
              wsize = sz;
              wnsol = nsol;
              wlevel = e.tlevel;
              wobs = List.exists D.obsolete atoms;
              watoms = atoms;
            })
        else if not opt then
          (* apt's Enqueue is of the clause's one live solution, not of the
             clause: the alternative's own name takes the slot too, ahead of
             any bare dependency that would reach it later; and where that
             solution is a version var, the version's pop takes the slot and
             the package var follows it *)
          match D.head assigned atoms with
          | Some (h, Some (orig, pv))
            when (not (Hashtbl.mem t.pos orig))
                 && not (Hashtbl.mem t.pending orig) ->
              if not (D.same_name h g) then enqueue t (Some e) g;
              Hashtbl.replace t.pending orig ();
              t.clock <- t.clock + 1;
              dbg "VQ1 #%d %a -> %a@." t.clock D.pp_name g D.pp_name orig;
              Queue.add (t.clock, VerFirst (e, orig, pv)) t.rq
          | Some (h, None) when not (D.same_name h g) ->
              enqueue t (Some e) g;
              if not (Hashtbl.mem t.pos h) then (
                Hashtbl.add t.pos h (Hashtbl.find t.pos g);
                e.tenq <- h :: e.tenq;
                dbg "INHERIT #%d %a -> %a@." (Hashtbl.find t.pos h) D.pp_name g
                  D.pp_name h)
          | _ -> enqueue t (Some e) g)

  (* a decided package's version var pops, and its watchers fire in an
     approximation of apt's registration order: the declarers of a conflict
     it matches, discovered alongside it as alternatives of the same clauses,
     lose their package var; the version's own clause queues the package
     var, unless that popped first; then the clauses registered on the
     version are walked *)
  let version_pops t ~assigned (e : tentry) ?pkg_var pkg pv clauses =
    queue_rejections t (D.conflicted_by assigned pkg pv);
    (match pkg_var with Some f -> f () | None -> ());
    List.iter (clause t ~assigned e) clauses

  (* one entry reaches its turn in the queue: what it assigns joins the
     back, rejections and the solutions of clauses left unit alike *)
  let propagate_one t ~assigned top =
    let s, entry = Queue.pop t.rq in
    match entry with
    | Reject r ->
        t.c_prop <- t.c_prop + 1;
        t.epoch <- t.epoch + 1;
        dbg "PROP #%d %a@." s D.pp_rejection r;
        let rs, units = D.propagate assigned r in
        queue_rejections t rs;
        List.iter (enqueue t top) units
    | VerOf (e, pv, clauses) ->
        dbg "VER #%d %a@." s D.pp_name e.tname;
        version_pops t ~assigned e e.tname pv clauses
    | VerFirst (e, orig, pv) ->
        dbg "VER1 #%d %a@." s D.pp_name orig;
        Hashtbl.remove t.pending orig;
        Hashtbl.replace t.ver_done orig ();
        e.tvd <- orig :: e.tvd;
        version_pops t ~assigned e
          ~pkg_var:(fun () -> enqueue t (Some e) orig)
          orig pv
          (snd (D.wave orig pv))

  (* Solver::Pop for one level: UndoOne re-AddWorks the level's popped items
     newest first (recounting size; a statically-unit hard clause is
     enqueued, i.e. left to tier 0), then items above the level are erased
     and the heap rebuilt. *)
  let forget_negations t lvl =
    t.negations <- List.filter (fun (l, _) -> l < lvl) t.negations

  let unwind_level t ~assigned lvl =
    t.c_unwind <- t.c_unwind + 1;
    forget_negations t lvl;
    (match Hashtbl.find_opt t.popped_at lvl with
    | Some r ->
        List.iter
          (fun (w : witem) ->
            if w.wopt || w.wnsol > 1 then (
              t.c_readd <- t.c_readd + 1;
              hpush t { w with wsize = live_size ~assigned w.watoms }))
          !r;
        Hashtbl.remove t.popped_at lvl
    | None -> ());
    herase t (fun w -> w.wlevel <= lvl - 1)

  (* what the standing decisions reject, derived afresh after a Pop has
     unassigned a level's rejections, and propagated through; the queue's
     pending part is lost with the conflict, except that a standing
     decision's version var still owes its clauses *)
  let replay t ~assigned =
    let standing =
      Queue.fold
        (fun acc (_, en) ->
          match en with
          | (VerOf (e, _, _) | VerFirst (e, _, _)) when e.tidx < t.tlen ->
              en :: acc
          | _ -> acc)
        [] t.rq
    in
    Queue.clear t.rq;
    Hashtbl.reset t.pending;
    t.epoch <- t.epoch + 1;
    List.iter
      (function
        | VerOf (e, _, cl) -> List.iter (clause t ~assigned e) cl
        | VerFirst (e, orig, pv) ->
            Hashtbl.replace t.ver_done orig ();
            e.tvd <- orig :: e.tvd;
            enqueue t (Some e) orig;
            List.iter (clause t ~assigned e) (snd (D.wave orig pv))
        | Reject _ -> ())
      (List.rev standing);
    D.reset ();
    for i = 0 to t.waved_upto - 1 do
      let e = t.tarr.(i) in
      match e.tval with
      | Some pv ->
          queue_rejections t (D.conflicts assigned e.tname pv);
          queue_rejections t (D.conflicted_by assigned e.tname pv)
      | None -> ()
    done;
    List.iter
      (fun (_, rs) -> queue_rejections t (D.assign assigned rs))
      (List.rev t.negations);
    let top = if t.tlen > 0 then Some t.tarr.(t.tlen - 1) else None in
    while not (Queue.is_empty t.rq) do
      propagate_one t ~assigned top
    done

  let drop_entries t from =
    for i = t.tlen - 1 downto from do
      let e = t.tarr.(i) in
      List.iter (Hashtbl.remove t.pos) e.tenq;
      List.iter (Hashtbl.remove t.ver_done) e.tvd;
      if e.tredo then (
        e.tredo <- false;
        t.nredo <- t.nredo - 1;
        Hashtbl.remove t.keep e.tname)
    done;
    t.tlen <- from;
    if t.waved_upto > t.tlen then t.waved_upto <- t.tlen

  (* A fallen suffix of the trail is a PubGrub backjump.  apt's Pop undoes
     exactly one level and asserts the negation of its choice (solver3.cc);
     PubGrub's conflict resolution jumps to the previous satisfier's level,
     which may be lower.  The levels apt keeps are kept here too: their
     entries stay on the trail as decisions to make again, first and to the
     same versions, their slots, work items and rejections untouched.  Only
     the topmost level is unwound.  A redo entry PubGrub decides otherwise,
     or a fall with no wide decision in it, is beyond that: the whole suffix
     is unwound level by level, as before. *)
  let sync t ~assigned =
    let cut = ref t.tlen in
    let brk = ref false in
    while (not !brk) && !cut > 0 do
      if standing t ~assigned t.tarr.(!cut - 1) then brk := true else decr cut
    done;
    if !cut < t.tlen then (
      t.c_fall <- t.c_fall + 1;
      let fallen_redo = ref false and top_wide = ref (-1) in
      for i = !cut to t.tlen - 1 do
        let e = t.tarr.(i) in
        if e.tredo then fallen_redo := true;
        if e.twide && e.tlevel = t.wide_count then top_wide := i
      done;
      (* an entry PubGrub never assigned -- its decision refused on the spot
         as conflicting -- is no choice of apt's to negate or to redo *)
      let value i =
        let e = t.tarr.(i) in
        match e.tval with Some v -> Some (e, v) | None -> None
      in
      match
        if (not !fallen_redo) && !top_wide >= !cut then value !top_wide else None
      with
      | Some (m, mv) ->
          (* apt's choice is the alternative's own solution, decided as the
           pending half of the same step where the wide decision is a clause *)
          let choice =
            let rec go i =
              if i >= t.tlen then (m.tname, mv)
              else
                match value i with
                | Some (e, v)
                  when List.exists (D.same_name e.tname)
                         (D.continuation m.tname mv) ->
                    (e.tname, v)
                | _ -> go (i + 1)
            in
            go (!top_wide + 1)
          in
          for i = !cut to !top_wide - 1 do
            match value i with
            | Some (e, v) when not e.tredo ->
                e.tredo <- true;
                t.nredo <- t.nredo + 1;
                Hashtbl.replace t.keep e.tname v;
                dbg "REDO %a@." D.pp_name e.tname
            | _ -> ()
          done;
          drop_entries t !top_wide;
          forget_negations t m.tlevel;
          replay t ~assigned;
          unwind_level t ~assigned m.tlevel;
          t.wide_count <- t.wide_count - 1;
          dbg "POPLEVEL %d %a@." m.tlevel D.pp_name (fst choice);
          let rs = D.negation assigned (fst choice) (snd choice) in
          t.negations <- (t.wide_count, rs) :: t.negations;
          queue_rejections t (D.assign assigned rs)
      | None ->
          for i = t.tlen - 1 downto !cut do
            let e = t.tarr.(i) in
            if e.twide then (
              unwind_level t ~assigned e.tlevel;
              t.wide_count <- t.wide_count - 1)
          done;
          drop_entries t !cut;
          replay t ~assigned)

  (* the propagation wave of each standing decision, the clauses of a decided
     package in field order as Solver::Propagate walks its watches when the
     package var pops: its version var is queued first, then the Depends,
     then what its Conflicts and Breaks reject -- assigned before the
     Recommends are counted, since the negatives sit between the two in the
     cache's field order -- and the Recommends go to the heap *)
  let wave t ~assigned =
    for i = t.waved_upto to t.tlen - 1 do
      let e = t.tarr.(i) in
      match e.tval with
      | None -> ()
      | Some pv ->
          (match D.forced_to e.tname pv with
          | Some n
            when Hashtbl.mem t.pos e.tname
                 && (not (Hashtbl.mem t.pos n))
                 && not (Hashtbl.mem t.pending n) ->
              (* the package takes the selector's slot: apt enqueued its
                 package var there *)
              Hashtbl.add t.pos n (Hashtbl.find t.pos e.tname);
              e.tenq <- n :: e.tenq;
              dbg "INHERIT #%d %a -> %a@." (Hashtbl.find t.pos n) D.pp_name
                e.tname D.pp_name n
          | _ -> ());
          (match D.version_of e.tname pv with
          | Some (orig, ov) ->
              (* the selector's slot was the version var's: it pops here *)
              dbg "VER %a@." D.pp_name orig;
              version_pops t ~assigned e
                ~pkg_var:(fun () -> enqueue t (Some e) orig)
                orig ov
                (snd (D.wave orig ov));
              Hashtbl.replace t.ver_done orig ();
              e.tvd <- orig :: e.tvd
          | None -> ());
          let pkg_clauses, ver_clauses = D.wave e.tname pv in
          if D.kind e.tname = Package then
            if e.tidx = 0 then
              (* the goal: the request enqueued its version var, which
                 popped first and queued the package var behind the
                 clauses registered on the version *)
              version_pops t ~assigned e e.tname pv ver_clauses
            else if Hashtbl.mem t.ver_done e.tname then
              Hashtbl.remove t.ver_done e.tname
            else (
              t.clock <- t.clock + 1;
              dbg "VQ #%d %a@." t.clock D.pp_name e.tname;
              Queue.add (t.clock, VerOf (e, pv, ver_clauses)) t.rq);
          let hard, soft =
            List.partition (fun (opt, _, _) -> not opt) pkg_clauses
          in
          List.iter (clause t ~assigned e) hard;
          queue_rejections t (D.conflicts assigned e.tname pv);
          List.iter (clause t ~assigned e) soft;
          (* apt's Assume of the chosen alternative queues it *)
          List.iter (enqueue t (Some e)) (D.continuation e.tname pv)
    done;
    t.waved_upto <- t.tlen

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
      tpush t
        {
          tname = n;
          tval = None;
          twide = wide;
          tlevel = lvl;
          tidx = t.tlen;
          tenq = [];
          tvd = [];
          tredo = false;
        };
      n
    in
    (* tier 0: apt's Enqueues -- hard clauses down to one live
       solution, and an optional clause with none left, which only its escape
       can settle -- drained in queue order, the rejections queued among them
       propagated as their slots come up, each queueing what it rejects and
       the last solution of any clause it leaves unit behind everything
       already there.  A name with a slot was queued by a wave that found it
       unit, and stays so: nothing rejected comes back short of a backjump,
       which forgets the slot.  A name found unit without a slot became so
       outside any wave (the provider a selector just resolved to, which
       apt reaches through the version's own SelectVersion clause) and is
       queued now, at the back. *)
    let redo =
      if t.nredo = 0 then None
      else
        let r = ref None in
        for i = 0 to t.tlen - 1 do
          let e = t.tarr.(i) in
          if !r = None && e.tredo && Hashtbl.mem offered e.tname then
            r := Some e.tname
        done;
        !r
    in
    match redo with
    | Some n ->
        dbg "REDECIDE %a@." D.pp_name n;
        n
    | None -> (
        let top = if t.tlen > 0 then Some t.tarr.(t.tlen - 1) else None in
        let unit_now (n, c) =
          match D.kind n with
          | Soft -> live_of_name t ~assigned n <= 0
          | Hard -> static_nsol t n <= 1 || live_of_name t ~assigned n <= 1
          | Alternative ->
              (* one live target package is apt's Enqueue: Strict-Pinning
             leaves each package one live version, so apt's count of version
             vars is this count of packages *)
              c < 2 || live_of_name t ~assigned n <= 1
          | Package ->
              (* a package brought in is apt's Enqueue of its var; under
             Strict-Pinning the SelectVersion item apt defers the version
             pick to has only the candidate left *)
              true
        in
        let slot_units () =
          List.iter
            (fun ((n, c) as nc) ->
              if (not (Hashtbl.mem t.pos n)) && not (Hashtbl.mem t.pending n)
              then
                match Hashtbl.find_opt t.nonunit n with
                | Some (c', e) when c' = c && e = t.epoch -> ()
                | _ ->
                    if unit_now nc then enqueue t top n
                    else Hashtbl.replace t.nonunit n (c, t.epoch))
            open_names
        in
        let rec drain () =
          let cand =
            List.fold_left
              (fun acc (n, _) ->
                match Hashtbl.find_opt t.pos n with
                | None -> acc
                | Some s -> (
                    match acc with
                    | Some (_, d) when d <= s -> acc
                    | _ -> Some (n, s)))
              None open_names
          in
          match Queue.peek_opt t.rq with
          | Some (s, _)
            when match cand with None -> true | Some (_, d) -> s < d ->
              propagate_one t ~assigned top;
              drain ()
          | _ -> cand
        in
        slot_units ();
        let t0 = drain () in
        match t0 with
        | Some (n, _) ->
            t.c_t0 <- t.c_t0 + 1;
            ret ~wide:false n
        | None -> (
            let rec pop () =
              if t.hlen = 0 then None
              else
                let w = hpop t in
                if Hashtbl.mem offered w.wname then
                  if D.satisfied assigned w.wname then (
                    (* apt's ELIDED opens no level; PubGrub still has to
                       decide the name, to the carried alternative *)
                    t.c_elide <- t.c_elide + 1;
                    dbg "ELIDE (%d/%d@%d) %a [%a]@." w.wsize w.wnsol w.wlevel
                      D.pp_name w.wname watoms w.wname;
                    record_popped t t.wide_count w;
                    Some (ret ~wide:false w.wname))
                  else if w.wopt && live_size ~assigned w.watoms <= 0 then (
                    (* an optional item every solution of which is false is
                   dropped, and opens no level either; PubGrub decides the
                   name to its escape *)
                    t.c_drop <- t.c_drop + 1;
                    dbg "DROP (%d/%d@%d) %a [%a]@." w.wsize w.wnsol w.wlevel
                      D.pp_name w.wname watoms w.wname;
                    record_popped t t.wide_count w;
                    Some (ret ~wide:false w.wname))
                  else (
                    t.c_pop <- t.c_pop + 1;
                    dbg "POP (%d/%d@%d) %a [%a]@." w.wsize w.wnsol w.wlevel
                      D.pp_name w.wname watoms w.wname;
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
                (* apt would have nothing left to do while PubGrub has a
                   name open, so the two have parted: PubGrub's own pick *)
                t.c_desync <- t.c_desync + 1;
                let n = fst (List.hd open_names) in
                dbg "DESYNC-EMPTY %a (open %d)@." D.pp_name n
                  (List.length open_names);
                ret ~wide:true n))

  let report t =
    if Sys.getenv_opt "PACSHADOW" <> None then
      Printf.eprintf
        "PACSHADOW tier0=%d pop=%d elide=%d drop=%d desync=%d \
         push=%d readd=%d unwind=%d backjump=%d prop=%d\n\
         %!"
        t.c_t0 t.c_pop t.c_elide t.c_drop t.c_desync t.c_push t.c_readd
        t.c_unwind t.c_fall t.c_prop
end
