(* libstdc++'s binary heap (bits/stl_heap.h), reproduced exactly: a
   comparator whose ties nothing else settles leaves the order to the way
   equal elements travel, which a textbook sift-down would change. *)
type 'a t = {
  less : 'a -> 'a -> bool;
  mutable arr : 'a array;
  mutable len : int;
}

let create less = { less; arr = [||]; len = 0 }
let length h = h.len

(* room for one more element, the fresh cells filled with [x] *)
let grow arr len x =
  if len < Array.length arr then arr
  else
    let na = Array.make (max 256 (2 * len)) x in
    Array.blit arr 0 na 0 len;
    na

(* __push_heap *)
let rec sift_up h hole top value =
  let parent = (hole - 1) / 2 in
  if hole > top && h.less h.arr.(parent) value then (
    h.arr.(hole) <- h.arr.(parent);
    sift_up h parent top value)
  else h.arr.(hole) <- value

(* __adjust_heap: the hole walks to a leaf along the greater child -- the
   right one when they tie -- and the displaced value is then sifted back
   up *)
let adjust h top len value =
  let a = h.arr in
  let rec down hole =
    if hole < (len - 1) / 2 then (
      let child = 2 * (hole + 1) in
      let child = if h.less a.(child) a.(child - 1) then child - 1 else child in
      a.(hole) <- a.(child);
      down child)
    else hole
  in
  let hole = down top in
  let hole =
    if len land 1 = 0 && hole = (len - 2) / 2 then (
      let child = 2 * (hole + 1) in
      a.(hole) <- a.(child - 1);
      child - 1)
    else hole
  in
  sift_up h hole top value

let push h x =
  h.arr <- grow h.arr h.len x;
  h.arr.(h.len) <- x;
  h.len <- h.len + 1;
  sift_up h (h.len - 1) 0 x

let pop h =
  let a = h.arr in
  let front = a.(0) in
  if h.len > 1 then (
    let value = a.(h.len - 1) in
    a.(h.len - 1) <- a.(0);
    adjust h 0 (h.len - 1) value);
  h.len <- h.len - 1;
  front

(* __make_heap *)
let make h =
  if h.len >= 2 then
    for parent = (h.len - 2) / 2 downto 0 do
      adjust h parent h.len h.arr.(parent)
    done

(* std::remove_if, which is stable, then std::make_heap *)
let filter h keep =
  let a = h.arr in
  let j = ref 0 in
  for i = 0 to h.len - 1 do
    if keep a.(i) then (
      a.(!j) <- a.(i);
      incr j)
  done;
  h.len <- !j;
  make h
