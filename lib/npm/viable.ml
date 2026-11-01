module Make
    (Encoding : Encoding.S)
    (L : module type of Lookup.Make (Encoding)) =
struct
  open Encoding

  let is_orig = function Np.Version.Orig _ -> true | _ -> false

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
      | _, PG.Decided (Np.Version.Orig w) -> Some (PVersion.equal (Np.Version.Orig w))
      | Np.Name.Link (_, _, m, u, a), PG.Entailed r
        when not (PG.Ranges.contains Np.Version.Bot r) -> (
          match assigned (Np.Name.Sight (m, u, a)) with
          | PG.Decided (Np.Version.Orig y) -> Some (PVersion.equal (Np.Version.Orig y))
          | _ -> Some (fun x -> PG.Ranges.contains x r))
      | _ -> None
    in
    match n with
    | Np.Name.Link (k, v, m, u, a) -> (
        match L.holder st (k, v) a with
        | None -> cands
        | Some h ->
            let s = Np.Name.Sight (m, u, a) in
            let ok x =
              match x with
              | Np.Version.Bot ->
                  within assigned s Np.Version.Bot || within assigned s Np.Version.Free
              | Np.Version.Orig _ ->
                  within assigned h x
                  && (within assigned s x || within assigned s Np.Version.Free)
              | Np.Version.Free -> false
            in
            let unopened =
              match assigned h with PG.Unselected -> true | _ -> false
            in
            if unopened && List.mem Np.Version.Bot cands && ok Np.Version.Bot then
              [ Np.Version.Bot ]
            else keep ok)
    | Np.Name.Intermediate (k, v, m) -> (
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
                x = Np.Version.Bot
                || within assigned d x
                   && List.for_all
                        (fun s ->
                          match assigned s with
                          | PG.Decided Np.Version.Bot -> true
                          | _ -> within assigned s x)
                        sibs
          | None -> fun _ -> true
        in
        match List.filter_map binds (L.links_into st n) with
        | [] -> keep desc_ok
        | bs ->
            keep (fun x ->
                is_orig x && desc_ok x && List.for_all (fun b -> b x) bs))
    | Np.Name.Sight _ -> (
        (* a link reading the sight fixes it, Bot included *)
        let reads l =
          match assigned l with
          | PG.Decided x -> Some (PVersion.equal x)
          | _ -> binds l
        in
        match List.filter_map reads (L.links_into st n) with
        | [] -> cands
        | bs -> keep (fun x -> List.for_all (fun b -> b x) bs))
    | Np.Name.Granular _ | Np.Name.Desc _ -> cands
end
