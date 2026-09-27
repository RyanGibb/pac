open Encoding
module L = Lookup

let is_orig = function Np.Vs.Orig _ -> true | _ -> false

let within (assigned : PName.t -> PG.selection) n x =
  match assigned n with
  | PG.Entailed r -> PG.Ranges.contains x r
  | PG.Decided y -> PVersion.equal x y
  | PG.Unselected -> true

let viable st ~assigned (n : PName.t) cands =
  let keep ok = match List.filter ok cands with [] -> cands | l -> l in
  (* what a link into a directory asks of it, when it cannot be Bot *)
  let binds l =
    match (l, assigned l) with
    | _, PG.Decided (Np.Vs.Orig w) -> Some (PVersion.equal (Np.Vs.Orig w))
    | Np.Nm.Link (_, _, m, u, a), PG.Entailed r
      when not (PG.Ranges.contains Np.Vs.Bot r) -> (
        match assigned (Np.Nm.Sight (m, u, a)) with
        | PG.Decided (Np.Vs.Orig y) -> Some (PVersion.equal (Np.Vs.Orig y))
        | _ -> Some (fun x -> PG.Ranges.contains x r))
    | _ -> None
  in
  match n with
  | Np.Nm.Link (k, v, m, u, a) -> (
      match L.holder st (k, v) a with
      | None -> cands
      | Some h ->
          let s = Np.Nm.Sight (m, u, a) in
          let ok x =
            match x with
            | Np.Vs.Bot ->
                within assigned s Np.Vs.Bot || within assigned s Np.Vs.Free
            | Np.Vs.Orig _ ->
                within assigned h x
                && (within assigned s x || within assigned s Np.Vs.Free)
            | Np.Vs.Free -> false
          in
          let unopened =
            match assigned h with PG.Unselected -> true | _ -> false
          in
          if unopened && List.mem Np.Vs.Bot cands && ok Np.Vs.Bot then
            [ Np.Vs.Bot ]
          else keep ok)
  | Np.Nm.Intermediate (k, v, m) -> (
      (* one version per descriptor (the shared reading): what another
         directory reading it has decided binds this one, and so does what
         the others' own constraints leave open, since a pick outside it
         rules out only itself *)
      let desc_ok =
        match L.desc_name st (snd k, v) m with
        | Some d ->
            let sibs =
              List.filter (fun s -> PName.compare s n <> 0) (L.desc_dirs st d)
            in
            fun x ->
              x = Np.Vs.Bot
              || within assigned d x
                 && List.for_all
                      (fun s ->
                        match assigned s with
                        | PG.Decided Np.Vs.Bot -> true
                        | _ -> within assigned s x)
                      sibs
        | None -> fun _ -> true
      in
      match List.filter_map binds (L.links_into st n) with
      | [] -> keep desc_ok
      | bs ->
          keep (fun x ->
              is_orig x && desc_ok x && List.for_all (fun b -> b x) bs))
  | Np.Nm.Sight _ -> (
      (* a link reading the sight fixes it, Bot included *)
      let reads l =
        match assigned l with
        | PG.Decided x -> Some (PVersion.equal x)
        | _ -> binds l
      in
      match List.filter_map reads (L.links_into st n) with
      | [] -> cands
      | bs -> keep (fun x -> List.for_all (fun b -> b x) bs))
  | Np.Nm.Granular _ | Np.Nm.Desc _ -> cands
