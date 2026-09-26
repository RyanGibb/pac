(* The split apt makes between what it unit-propagates (Enqueue) and what it
   queues as a work item, seen through the synthetic names of the
   encoding. *)
type kind =
  (* a real package name: apt enqueues the package var *)
  | Package
  (* a clause package whose Clause has eager = true *)
  | Hard
  (* an optional (Recommends) clause package *)
  | Soft
  (* a lone alternative standing in for its own clause *)
  | Alternative

(* One clause of a decided package as apt registers it: [name] stands for
   it -- its clause package, or the one target of a bare Depends, which apt
   enqueues rather than queues as work -- and is None for a clause folded
   into an earlier one. *)
type ('name, 'atom) clause = {
  optional : bool;
  name : 'name option;
  atoms : 'atom list;
}

(* the one live alternative of a clause found unit, apt's Enqueue of that
   solution, with the package and candidate version it stands for where the
   solution is a version var *)
type ('name, 'version) unit_head = {
  solution : 'name;
  version_var : ('name * 'version) option;
}

module type DRIVER = sig
  (* the rejections assigned so far, and what the driver caches over the
     instance *)
  type state
  type name
  type version
  type atom

  (* what the partial solution says about a name, as the solver hands it to
     the [next] hook *)
  type assigned

  val pp_name : Format.formatter -> name -> unit
  val pp_atom : Format.formatter -> atom -> unit
  val kind : name -> kind

  (* the alternatives of the clause [name] stands for *)
  val clause_atoms : name -> atom list option

  (* apt's solution count for one alternative: the target packages it can
     still be discharged by, live under the partial solution and over the
     candidates-only instance respectively (apt's static count also takes
     in the versions Strict-Pinning rejected) *)
  val solutions : state -> assigned:assigned -> atom -> int
  val static_solutions : state -> atom -> int

  (* some package the alternative can be discharged by is obsolete to apt
     (Obsolete, solver3.cc:890-925): a binary of its source comes from a
     newer source version *)
  val obsolete : atom -> bool

  (* the value the partial solution has decided [name] at, if any *)
  val decided : assigned -> name -> version option

  (* apt's ELIDED: some solution of the clause [name] stands for is already
     in the partial solution, so deciding it installs nothing *)
  val satisfied : assigned -> name -> bool

  (* one entry of apt's propagation queue that is a rejection: a literal
     assigned false the moment it was derived, and propagated to what
     watches it only when the queue reaches it *)
  type rejection

  val pp_rejection : Format.formatter -> rejection -> unit

  (* a package decision now stands: the rejections its own Conflicts assign
     as its clauses are examined, and those assigned as its version var
     propagates -- the declarers of a conflict it matches -- each to be
     queued for propagation at that point; [propagate] runs one entry,
     assigning and returning the rejections it derives in turn, with the
     clauses of installed packages it leaves unit, whose one solution apt
     enqueues there and then; [reset] forgets every rejection, ahead of the
     standing decisions being replayed; [assign] assigns rejections derived
     outside the driver's own propagation, as [conflicts] assigns its own:
     those not already assigned, and not of a package the partial solution
     installs *)
  val conflicts :
    state -> assigned:assigned -> name -> version -> rejection list

  val conflicted_by :
    state -> assigned:assigned -> name -> version -> rejection list

  val propagate :
    state -> assigned:assigned -> rejection -> rejection list * name list

  val reset : state -> unit
  val assign : state -> assigned:assigned -> rejection list -> rejection list
  val version_equal : version -> version -> bool

  (* the propagation wave a standing decision sets off: the decided
     package's clauses in control-file order, first those apt registers on
     the package var, walked as the package pops, then those it registers
     on the version var, walked one queue entry later as the version pops *)
  val registered :
    state ->
    name ->
    version ->
    (name, atom) clause list * (name, atom) clause list

  (* what apt's Assume of the alternative a clause was decided to enqueues:
     its selector, or its package where the alternative is deferred *)
  val continuation : name -> version -> name list

  (* the package a decided selector forces, where apt would have enqueued
     that package at the selector's own queue slot rather than reaching it
     through a version's SelectVersion clause at the back *)
  val forced_to : state -> name -> version -> name option

  (* the package and version a decided selector settles on, where that
     decision is apt's version var popping: the clauses registered on the
     version are walked then, and its package var joins the queue *)
  val version_of : state -> name -> version -> (name * version) option

  (* the unit head of a clause found unit: its version var is there only
     for an atom neither deferred nor matched by a provider, whose package
     var apt reaches only as the version pops *)
  val head :
    state -> assigned:assigned -> atom list -> (name, version) unit_head option

  val same_name : name -> name -> bool

  (* the literal apt's Pop asserts against a decision it undoes: the
     solution the decision installed, rejected *)
  val negation : state -> assigned:assigned -> name -> version -> rejection list
end

module Make (D : DRIVER) = struct
  (* A work item of apt's Solver::Work (solver3.cc): size is the live
     solution count frozen at push, nsol the clause's static solution count,
     level the wide-decision depth at push.  eager is not stored because it
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
    | VerOf of tentry * D.version * (D.name, D.atom) clause list
    (* a version var apt enqueued as a clause's one solution: its pop queues
       the package var and walks the version's clauses *)
    | VerFirst of tentry * D.name * D.version

  (* scheduling counters, reported under PACSHADOW *)
  type stats = {
    mutable t0 : int;
    mutable prop : int;
    mutable pop : int;
    mutable elide : int;
    mutable drop : int;
    mutable desync : int;
    mutable push : int;
    mutable readd : int;
    mutable unwind : int;
    (* PubGrub backjumps seen, whether or not a level fell with them *)
    mutable fall : int;
  }

  type t = {
    d : D.state;
    (* apt's propagation queue (propQ, solver3.cc) as the slot each name was
       enqueued at: a wave's unit clauses append their solution in field
       order, behind everything queued before, and the tier-0 drain takes
       the smallest slot.  A name is queued only when apt would Enqueue it,
       so an alternative of a wide clause has no slot until that clause is
       decided to it. *)
    pos : (D.name, int) Hashtbl.t;
    mutable clock : int;
    heap : witem Stl_heap.t;
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
    stats : stats;
  }

  (* Work::operator< (solver3.cc:60): a is less important than b *)
  let wless a b =
    let ua = (not a.wopt) && a.wsize < 2 and ub = (not b.wopt) && b.wsize < 2 in
    if ua <> ub then ub
    else if a.wopt <> b.wopt then a.wopt (* eager = not optional *)
    else if a.wobs <> b.wobs then a.wobs
    else if a.wsize < 2 <> (b.wsize < 2) then b.wsize < 2
    else if a.wsize = 1 && b.wsize = 1 then a.wnsol < b.wnsol
    else false

  let create d =
    {
      d;
      pos = Hashtbl.create 4096;
      clock = 0;
      heap = Stl_heap.create wless;
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
      stats =
        {
          t0 = 0;
          prop = 0;
          pop = 0;
          elide = 0;
          drop = 0;
          desync = 0;
          push = 0;
          readd = 0;
          unwind = 0;
          fall = 0;
        };
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

  let static_nsol_atoms t atoms =
    List.fold_left (fun acc a -> acc + D.static_solutions t.d a) 0 atoms

  let static_nsol t n =
    match Hashtbl.find_opt t.nsol_tbl n with
    | Some k -> k
    | None ->
        let k =
          match D.clause_atoms n with
          | Some atoms -> static_nsol_atoms t atoms
          | None -> max_int
        in
        Hashtbl.add t.nsol_tbl n k;
        k

  let live_size t ~assigned atoms =
    (* only < 2 and = 1 matter to the comparator, so cap the count *)
    let rec go acc = function
      | [] -> acc
      | _ when acc >= 2 -> acc
      | a :: rest -> go (acc + D.solutions t.d ~assigned a) rest
    in
    go 0 atoms

  let live_of_name t ~assigned n =
    match Hashtbl.find_opt t.atoms_tbl n with
    | Some atoms -> live_size t ~assigned atoms
    | None -> (
        match D.clause_atoms n with
        | Some atoms -> live_size t ~assigned atoms
        | None -> 0)

  let tpush t e =
    t.tarr <- Stl_heap.grow t.tarr t.tlen e;
    t.tarr.(t.tlen) <- e;
    t.tlen <- t.tlen + 1

  let top t = if t.tlen > 0 then Some t.tarr.(t.tlen - 1) else None

  let record_popped t w =
    let lvl = t.wide_count in
    match Hashtbl.find_opt t.popped_at lvl with
    | Some r -> r := w :: !r
    | None -> Hashtbl.add t.popped_at lvl (ref [ w ])

  let finish_redo t (e : tentry) =
    e.tredo <- false;
    t.nredo <- t.nredo - 1;
    Hashtbl.remove t.keep e.tname

  (* a trail entry still stands if PubGrub has it decided at the value it
     had, or has it undone for now but apt keeps it (a redo) *)
  let standing ~assigned (e : tentry) =
    match D.decided assigned e.tname with
    | None -> e.tredo
    | Some pv -> (
        match e.tval with Some pv' -> D.version_equal pv pv' | None -> true)

  (* what the topmost standing entry learns from PubGrub: its value when
     first decided, and that a redo has been made again *)
  let settle t ~assigned (e : tentry) =
    match D.decided assigned e.tname with
    | None -> ()
    | Some pv -> (
        match e.tval with
        | None -> e.tval <- Some pv
        | Some pv' -> if e.tredo && D.version_equal pv pv' then finish_redo t e)

  let kept t n = Hashtbl.find_opt t.keep n

  let push_item t (e : tentry) (c : (D.name, D.atom) clause) g nsol sz =
    t.stats.push <- t.stats.push + 1;
    dbg "PUSH (%d/%d@%d)%s %a -> %a [%a]@." sz nsol e.tlevel
      (if c.optional then " opt" else "")
      D.pp_name e.tname D.pp_name g watoms g;
    Stl_heap.push t.heap
      {
        wname = g;
        wopt = c.optional;
        wsize = sz;
        wnsol = nsol;
        wlevel = e.tlevel;
        wobs = List.exists D.obsolete c.atoms;
        watoms = c.atoms;
      }

  (* apt's Enqueue is of the clause's one live solution, not of the
     clause: the alternative's own name takes the slot too, ahead of any
     bare dependency that would reach it later; and where that solution is a
     version var, the version's pop takes the slot and the package var
     follows it *)
  let enqueue_unit t ~assigned (e : tentry) atoms g =
    match D.head t.d ~assigned atoms with
    | Some { solution = h; version_var = Some (orig, pv) }
      when (not (Hashtbl.mem t.pos orig)) && not (Hashtbl.mem t.pending orig) ->
        if not (D.same_name h g) then enqueue t (Some e) g;
        Hashtbl.replace t.pending orig ();
        t.clock <- t.clock + 1;
        dbg "VQ1 #%d %a -> %a@." t.clock D.pp_name g D.pp_name orig;
        Queue.add (t.clock, VerFirst (e, orig, pv)) t.rq
    | Some { solution = h; version_var = None } when not (D.same_name h g) ->
        enqueue t (Some e) g;
        if not (Hashtbl.mem t.pos h) then (
          Hashtbl.add t.pos h (Hashtbl.find t.pos g);
          e.tenq <- h :: e.tenq;
          dbg "INHERIT #%d %a -> %a@." (Hashtbl.find t.pos h) D.pp_name g
            D.pp_name h)
    | _ -> enqueue t (Some e) g

  (* one clause of a decided package as Solver::Propagate meets it: a hard
     clause down to one live solution is apt's Enqueue and takes the next
     queue slot, any other live clause is a work item, and an optional clause
     nothing can satisfy any more is dropped *)
  let clause t ~assigned (e : tentry) (c : (D.name, D.atom) clause) =
    match c.name with
    | None -> ()
    | Some g ->
        let nsol = static_nsol_atoms t c.atoms in
        Hashtbl.replace t.nsol_tbl g nsol;
        Hashtbl.replace t.atoms_tbl g c.atoms;
        let sz = live_size t ~assigned c.atoms in
        if (c.optional && sz >= 1) || sz >= 2 then push_item t e c g nsol sz
        else if not c.optional then enqueue_unit t ~assigned e c.atoms g

  (* a decided package's version var pops, and its watchers fire in an
     approximation of apt's registration order: the declarers of a conflict
     it matches, discovered alongside it as alternatives of the same clauses,
     lose their package var; the version's own clause queues the package
     var, unless that popped first; then the clauses registered on the
     version are walked *)
  let version_pops t ~assigned (e : tentry) ?pkg_var pkg pv clauses =
    queue_rejections t (D.conflicted_by t.d ~assigned pkg pv);
    (match pkg_var with Some f -> f () | None -> ());
    List.iter (clause t ~assigned e) clauses

  (* one entry reaches its turn in the queue: what it assigns joins the
     back, rejections and the solutions of clauses left unit alike *)
  let propagate_one t ~assigned =
    let s, entry = Queue.pop t.rq in
    match entry with
    | Reject r ->
        t.stats.prop <- t.stats.prop + 1;
        t.epoch <- t.epoch + 1;
        dbg "PROP #%d %a@." s D.pp_rejection r;
        let rs, units = D.propagate t.d ~assigned r in
        queue_rejections t rs;
        List.iter (enqueue t (top t)) units
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
          (snd (D.registered t.d orig pv))

  let forget_negations t lvl =
    t.negations <- List.filter (fun (l, _) -> l < lvl) t.negations

  (* Solver::Pop for one level: UndoOne re-AddWorks the level's popped items
     newest first (recounting size; a statically-unit hard clause is
     enqueued, i.e. left to tier 0), then items above the level are erased
     and the heap rebuilt. *)
  let unwind_level t ~assigned lvl =
    t.stats.unwind <- t.stats.unwind + 1;
    forget_negations t lvl;
    (match Hashtbl.find_opt t.popped_at lvl with
    | Some r ->
        List.iter
          (fun (w : witem) ->
            if w.wopt || w.wnsol > 1 then (
              t.stats.readd <- t.stats.readd + 1;
              Stl_heap.push t.heap
                { w with wsize = live_size t ~assigned w.watoms }))
          !r;
        Hashtbl.remove t.popped_at lvl
    | None -> ());
    Stl_heap.filter t.heap (fun w -> w.wlevel <= lvl - 1)

  (* what the standing decisions reject, derived afresh after a Pop has
     unassigned a level's rejections, and propagated through, with the
     negations earlier Pops asserted at the levels that still stand; the
     queue's pending part is lost with the conflict, except that a standing
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
            List.iter (clause t ~assigned e) (snd (D.registered t.d orig pv))
        | Reject _ -> ())
      (List.rev standing);
    D.reset t.d;
    for i = 0 to t.waved_upto - 1 do
      let e = t.tarr.(i) in
      match e.tval with
      | Some pv ->
          queue_rejections t (D.conflicts t.d ~assigned e.tname pv);
          queue_rejections t (D.conflicted_by t.d ~assigned e.tname pv)
      | None -> ()
    done;
    List.iter
      (fun (_, rs) -> queue_rejections t (D.assign t.d ~assigned rs))
      (List.rev t.negations);
    while not (Queue.is_empty t.rq) do
      propagate_one t ~assigned
    done

  let drop_entries t from =
    for i = t.tlen - 1 downto from do
      let e = t.tarr.(i) in
      List.iter (Hashtbl.remove t.pos) e.tenq;
      List.iter (Hashtbl.remove t.ver_done) e.tvd;
      if e.tredo then finish_redo t e
    done;
    t.tlen <- from;
    if t.waved_upto > t.tlen then t.waved_upto <- t.tlen

  (* the trail entry at [i], if PubGrub ever assigned it: an entry whose
     decision was refused on the spot as conflicting is no choice of apt's
     to negate or to redo *)
  let value t i =
    let e = t.tarr.(i) in
    match e.tval with Some v -> Some (e, v) | None -> None

  (* apt's choice at the wide decision [m]: the alternative's own solution,
     decided as the pending half of the same step where the wide decision is
     a clause *)
  let choice_at t top_wide ((m : tentry), mv) =
    let rec go i =
      if i >= t.tlen then (m.tname, mv)
      else
        match value t i with
        | Some (e, v)
          when List.exists (D.same_name e.tname) (D.continuation m.tname mv) ->
            (e.tname, v)
        | _ -> go (i + 1)
    in
    go (top_wide + 1)

  (* apt's Pop of the top level, the wide decision [m] at [top_wide]: the
     levels below stay, their fallen entries to be redone *)
  let pop_level t ~assigned ~cut top_wide ((m : tentry), mv) =
    let choice = choice_at t top_wide (m, mv) in
    for i = cut to top_wide - 1 do
      match value t i with
      | Some (e, v) when not e.tredo ->
          e.tredo <- true;
          t.nredo <- t.nredo + 1;
          Hashtbl.replace t.keep e.tname v;
          dbg "REDO %a@." D.pp_name e.tname
      | _ -> ()
    done;
    drop_entries t top_wide;
    forget_negations t m.tlevel;
    replay t ~assigned;
    unwind_level t ~assigned m.tlevel;
    t.wide_count <- t.wide_count - 1;
    dbg "POPLEVEL %d %a@." m.tlevel D.pp_name (fst choice);
    (* Solver::Pop enqueues the negation of its choice at the level below
       (solver3.cc:517-519) *)
    let rs = D.negation t.d ~assigned (fst choice) (snd choice) in
    t.negations <- (t.wide_count, rs) :: t.negations;
    queue_rejections t (D.assign t.d ~assigned rs)

  (* the whole fallen suffix unwound level by level *)
  let unwind_all t ~assigned ~cut =
    for i = t.tlen - 1 downto cut do
      let e = t.tarr.(i) in
      if e.twide then (
        unwind_level t ~assigned e.tlevel;
        t.wide_count <- t.wide_count - 1)
    done;
    drop_entries t cut;
    replay t ~assigned

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
    let cut =
      let c = ref t.tlen in
      while !c > 0 && not (standing ~assigned t.tarr.(!c - 1)) do
        decr c
      done;
      !c
    in
    if cut > 0 then settle t ~assigned t.tarr.(cut - 1);
    if cut < t.tlen then (
      t.stats.fall <- t.stats.fall + 1;
      let fallen_redo = ref false and top_wide = ref (-1) in
      for i = cut to t.tlen - 1 do
        let e = t.tarr.(i) in
        if e.tredo then fallen_redo := true;
        if e.twide && e.tlevel = t.wide_count then top_wide := i
      done;
      match
        if (not !fallen_redo) && !top_wide >= cut then value t !top_wide
        else None
      with
      | Some m -> pop_level t ~assigned ~cut !top_wide m
      | None -> unwind_all t ~assigned ~cut)

  (* the selector's slot was its package's: apt enqueued the package var
     there *)
  let inherit_slot t (e : tentry) pv =
    match D.forced_to t.d e.tname pv with
    | Some n
      when Hashtbl.mem t.pos e.tname
           && (not (Hashtbl.mem t.pos n))
           && not (Hashtbl.mem t.pending n) ->
        Hashtbl.add t.pos n (Hashtbl.find t.pos e.tname);
        e.tenq <- n :: e.tenq;
        dbg "INHERIT #%d %a -> %a@." (Hashtbl.find t.pos n) D.pp_name e.tname
          D.pp_name n
    | _ -> ()

  (* the selector's slot was the version var's: it pops here *)
  let selector_version_pops t ~assigned (e : tentry) pv =
    match D.version_of t.d e.tname pv with
    | Some (orig, ov) ->
        dbg "VER %a@." D.pp_name orig;
        version_pops t ~assigned e
          ~pkg_var:(fun () -> enqueue t (Some e) orig)
          orig ov
          (snd (D.registered t.d orig ov));
        Hashtbl.replace t.ver_done orig ();
        e.tvd <- orig :: e.tvd
    | None -> ()

  (* a decided package's version var: the goal's popped first, the request
     having enqueued it, and queued the package var behind the clauses
     registered on the version; one reached through a selector has popped
     already; any other is queued now, behind the package's own wave *)
  let queue_version t ~assigned (e : tentry) pv ver_clauses =
    if e.tidx = 0 then version_pops t ~assigned e e.tname pv ver_clauses
    else if Hashtbl.mem t.ver_done e.tname then
      Hashtbl.remove t.ver_done e.tname
    else (
      t.clock <- t.clock + 1;
      dbg "VQ #%d %a@." t.clock D.pp_name e.tname;
      Queue.add (t.clock, VerOf (e, pv, ver_clauses)) t.rq)

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
          inherit_slot t e pv;
          selector_version_pops t ~assigned e pv;
          let pkg_clauses, ver_clauses = D.registered t.d e.tname pv in
          if D.kind e.tname = Package then
            queue_version t ~assigned e pv ver_clauses;
          let hard, soft =
            List.partition (fun c -> not c.optional) pkg_clauses
          in
          List.iter (clause t ~assigned e) hard;
          queue_rejections t (D.conflicts t.d ~assigned e.tname pv);
          List.iter (clause t ~assigned e) soft;
          (* apt's Assume of the chosen alternative queues it *)
          List.iter (enqueue t (Some e)) (D.continuation e.tname pv)
    done;
    t.waved_upto <- t.tlen

  (* a decision joins the trail; a wide one opens apt's next level *)
  let decide t ~wide n =
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

  (* the first redo entry PubGrub offers, to be decided again first *)
  let redo t offered =
    if t.nredo = 0 then None
    else
      let r = ref None in
      for i = 0 to t.tlen - 1 do
        let e = t.tarr.(i) in
        if !r = None && e.tredo && Hashtbl.mem offered e.tname then
          r := Some e.tname
      done;
      !r

  let unit_now t ~assigned (n, c) =
    match D.kind n with
    | Soft -> live_of_name t ~assigned n <= 0
    | Hard -> static_nsol t n <= 1 || live_of_name t ~assigned n <= 1
    | Alternative ->
        (* one live target package is apt's Enqueue: Strict-Pinning leaves
           each package one live version, so apt's count of version vars is
           this count of packages *)
        c < 2 || live_of_name t ~assigned n <= 1
    | Package ->
        (* a package brought in is apt's Enqueue of its var; under
           Strict-Pinning the SelectVersion item apt defers the version pick
           to has only the candidate left *)
        true

  (* A name found unit without a slot became so outside any wave (the
     provider a selector just resolved to, which apt reaches through the
     version's own SelectVersion clause) and is queued now, at the back. *)
  let slot_units t ~assigned open_names =
    List.iter
      (fun ((n, c) as nc) ->
        if (not (Hashtbl.mem t.pos n)) && not (Hashtbl.mem t.pending n) then
          match Hashtbl.find_opt t.nonunit n with
          | Some (c', e) when c' = c && e = t.epoch -> ()
          | _ ->
              if unit_now t ~assigned nc then enqueue t (top t) n
              else Hashtbl.replace t.nonunit n (c, t.epoch))
      open_names

  (* the open name at the smallest slot, the rejections and version pops
     queued ahead of it propagated first *)
  let rec drain t ~assigned open_names =
    let cand =
      List.fold_left
        (fun acc (n, _) ->
          match Hashtbl.find_opt t.pos n with
          | None -> acc
          | Some s -> (
              match acc with Some (_, d) when d <= s -> acc | _ -> Some (n, s)))
        None open_names
    in
    match Queue.peek_opt t.rq with
    | Some (s, _) when match cand with None -> true | Some (_, d) -> s < d ->
        propagate_one t ~assigned;
        drain t ~assigned open_names
    | _ -> Option.map fst cand

  (* apt's ELIDED and a dead optional item open no level; PubGrub still has
     to decide the name, to the alternative it holds or to its escape *)
  let take_item t ~assigned w =
    let note what =
      dbg "%s (%d/%d@%d) %a [%a]@." what w.wsize w.wnsol w.wlevel D.pp_name
        w.wname watoms w.wname
    in
    if D.satisfied assigned w.wname then (
      t.stats.elide <- t.stats.elide + 1;
      note "ELIDE";
      record_popped t w;
      decide t ~wide:false w.wname)
    else if w.wopt && live_size t ~assigned w.watoms <= 0 then (
      t.stats.drop <- t.stats.drop + 1;
      note "DROP";
      record_popped t w;
      decide t ~wide:false w.wname)
    else (
      t.stats.pop <- t.stats.pop + 1;
      note "POP";
      let n = decide t ~wide:true w.wname in
      record_popped t w;
      n)

  (* the heap's next item PubGrub has open; one it has not is already
     decided (ELIDED) or has parted from apt (DESYNC), and is passed over *)
  let rec pop_offered t ~assigned offered =
    if Stl_heap.length t.heap = 0 then None
    else
      let w = Stl_heap.pop t.heap in
      if Hashtbl.mem offered w.wname then Some (take_item t ~assigned w)
      else (
        (match D.decided assigned w.wname with
        | Some _ ->
            t.stats.elide <- t.stats.elide + 1;
            dbg "ELIDE (%d/%d@%d) %a@." w.wsize w.wnsol w.wlevel D.pp_name
              w.wname
        | None ->
            t.stats.desync <- t.stats.desync + 1;
            dbg "DESYNC (%d/%d@%d) %a@." w.wsize w.wnsol w.wlevel D.pp_name
              w.wname);
        record_popped t w;
        pop_offered t ~assigned offered)

  (* PubGrub's [next] hook: sync the trail against the partial solution
     (replaying any backjump as Solver::Pop), push the waves of the newly
     standing decisions -- their unit clauses' solutions into apt's
     propagation queue, the rest onto the heap -- then drain the queue
     before answering from the heap.  Tier 0 is apt's Enqueues -- hard
     clauses down to one live solution, and an optional clause with none
     left, which only its escape can settle -- drained in queue order, the
     rejections queued among them propagated as their slots come up.  A
     name with a slot was queued by a wave that found it unit, and stays
     so: nothing rejected comes back short of a backjump, which forgets the
     slot. *)
  let next t ~assigned open_names =
    sync t ~assigned;
    wave t ~assigned;
    let offered = Hashtbl.create 64 in
    List.iter (fun (n, c) -> Hashtbl.replace offered n c) open_names;
    match redo t offered with
    | Some n ->
        dbg "REDECIDE %a@." D.pp_name n;
        n
    | None -> (
        slot_units t ~assigned open_names;
        match drain t ~assigned open_names with
        | Some n ->
            t.stats.t0 <- t.stats.t0 + 1;
            decide t ~wide:false n
        | None -> (
            match pop_offered t ~assigned offered with
            | Some n -> n
            | None ->
                (* apt would have nothing left to do while PubGrub has a
                   name open, so the two have parted: PubGrub's own pick *)
                t.stats.desync <- t.stats.desync + 1;
                let n = fst (List.hd open_names) in
                dbg "DESYNC-EMPTY %a (open %d)@." D.pp_name n
                  (List.length open_names);
                decide t ~wide:true n))

  let report t =
    let s = t.stats in
    if Sys.getenv_opt "PACSHADOW" <> None then
      Printf.eprintf
        "PACSHADOW tier0=%d pop=%d elide=%d drop=%d desync=%d push=%d readd=%d \
         unwind=%d backjump=%d prop=%d\n\
         %!"
        s.t0 s.pop s.elide s.drop s.desync s.push s.readd s.unwind s.fall s.prop
end
