module Make
    (Encoding : Encoding.S)
    (L : module type of Lookup.Make (Encoding)) =
struct
  open Encoding

  let is_orig = function Npm.Version.Orig _ -> true | _ -> false

  let within (assigned : PName.t -> Resolver.selection) n x =
    match assigned n with
    | Resolver.Entailed r -> Resolver.Ranges.contains x r
    | Resolver.Decided y -> PVersion.equal x y
    | Resolver.Unselected -> true

  let viable st ~assigned (n : PName.t) cands =
    let keep ok = match List.filter ok cands with [] -> cands | l -> l in
    (* what a link into a directory asks of it, when it cannot be Bot *)
    let binds l =
      match (l, assigned l) with
      | _, Resolver.Decided (Npm.Version.Orig w) ->
          Some (PVersion.equal (Npm.Version.Orig w))
      | Npm.Name.Link (_, _, m, u, a), Resolver.Entailed r
        when not (Resolver.Ranges.contains Npm.Version.Bot r) -> (
          match assigned (Npm.Name.Sight (m, u, a)) with
          | Resolver.Decided (Npm.Version.Orig y) ->
              Some (PVersion.equal (Npm.Version.Orig y))
          | _ -> Some (fun x -> Resolver.Ranges.contains x r))
      | _ -> None
    in
    match n with
    | Npm.Name.Link (k, v, m, u, a) -> (
        match L.holder st (k, v) a with
        | None -> cands
        | Some h ->
            let s = Npm.Name.Sight (m, u, a) in
            let ok x =
              match x with
              | Npm.Version.Bot ->
                  within assigned s Npm.Version.Bot
                  || within assigned s Npm.Version.Free
              | Npm.Version.Orig _ ->
                  within assigned h x
                  && (within assigned s x || within assigned s Npm.Version.Free)
              | Npm.Version.Free -> false
            in
            let unopened =
              match assigned h with Resolver.Unselected -> true | _ -> false
            in
            if unopened && List.mem Npm.Version.Bot cands && ok Npm.Version.Bot
            then [ Npm.Version.Bot ]
            else keep ok)
    | Npm.Name.Intermediate (k, v, m) -> (
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
                x = Npm.Version.Bot
                || within assigned d x
                   && List.for_all
                        (fun s ->
                          match assigned s with
                          | Resolver.Decided Npm.Version.Bot -> true
                          | _ -> within assigned s x)
                        sibs
          | None -> fun _ -> true
        in
        match List.filter_map binds (L.links_into st n) with
        | [] -> keep desc_ok
        | bs ->
            keep (fun x ->
                is_orig x && desc_ok x && List.for_all (fun b -> b x) bs))
    | Npm.Name.Sight _ -> (
        (* a link reading the sight fixes it, Bot included *)
        let reads l =
          match assigned l with
          | Resolver.Decided x -> Some (PVersion.equal x)
          | _ -> binds l
        in
        match List.filter_map reads (L.links_into st n) with
        | [] -> cands
        | bs -> keep (fun x -> List.for_all (fun b -> b x) bs))
    | Npm.Name.Granular _ | Npm.Name.Desc _ -> cands
end
