type t = [ `Tool | `Pubgrub | `Random of int ]

type ('name, 'selection, 'version) hooks = {
  next : (assigned:('name -> 'selection) -> ('name * int) list -> 'name) option;
  choose :
    (assigned:('name -> 'selection) -> 'name -> 'version list -> 'version)
    option;
  finish : unit -> unit;
}

type ('ctx, 'name, 'selection, 'version) driver =
  t -> 'ctx -> ('name, 'selection, 'version) hooks

let make ?next ?choose ?(finish = ignore) () = { next; choose; finish }

let random seed =
  let st = Random.State.make [| seed |] in
  let pick l = List.nth l (Random.State.int st (List.length l)) in
  make
    ~next:(fun ~assigned:_ open_names -> fst (pick open_names))
    ~choose:(fun ~assigned:_ _ cands -> pick cands)
    ()

let greatest compare = function
  | [] -> invalid_arg "greatest"
  | c :: cs -> List.fold_left (fun a b -> if compare b a > 0 then b else a) c cs
