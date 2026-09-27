type t =
  | Str of string
  | Int of int
  | Float of float
  | Bool of bool
  | Date of string (* kept as text: nothing cargo resolves reads one *)
  | Arr of t list
  | Tbl of tbl
  | ATbl of tbl list ref

(* how a table came to be, which is what TOML lets define or extend it
   later: a header's parent may be defined by a header of its own once, a
   dotted key's parent may take further dotted keys and sub-table headers
   but no header of its own, and a header's table or an inline one no
   dotted key from outside, the inline one no sub-table header either *)
and origin = Implicit | Dotted | Header | Inline
and tbl = { mutable fields : (string * t) list; mutable origin : origin }

exception Error of string

val of_file : string -> tbl
