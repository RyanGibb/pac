(* Trusted (TCB) reading of the TOML 1.0 a Cargo.toml is written in.  The
   switch pac builds in has no TOML library, and a query's manifest is one
   small file, so this is a direct reader of the whole grammar rather than
   of the fields cargo reads: a field the query module does not model has
   to be seen to be refused, not skipped by a parser that stopped short.
   Date-times are kept as their text; nothing cargo resolves reads one. *)

type t =
  | Str of string
  | Int of int
  | Float of float
  | Bool of bool
  | Date of string
  | Arr of t list
  | Tbl of tbl
  | ATbl of tbl list ref

(* explicit: defined by its own [header] or as a value, so a second
   definition is the duplicate TOML forbids; an implicit table, made as
   the parent of a dotted key or header, may still be defined once *)
and tbl = { mutable fields : (string * t) list; mutable explicit : bool }

exception Error of string

let fail line fmt =
  Printf.ksprintf (fun s -> raise (Error (Printf.sprintf "line %d: %s" line s))) fmt

type st = { s : string; mutable i : int; mutable line : int }

let peek st = if st.i < String.length st.s then Some st.s.[st.i] else None

let peek_at st k =
  if st.i + k < String.length st.s then Some st.s.[st.i + k] else None

let adv st =
  (match peek st with Some '\n' -> st.line <- st.line + 1 | _ -> ());
  st.i <- st.i + 1

let starts st p =
  let n = String.length p in
  st.i + n <= String.length st.s && String.sub st.s st.i n = p

let skip_ws st =
  while match peek st with Some (' ' | '\t') -> true | _ -> false do
    adv st
  done

let skip_comment st =
  if peek st = Some '#' then
    while match peek st with Some '\n' | None -> false | _ -> true do
      adv st
    done

(* whitespace, newlines and comments, as between array elements *)
let skip_blank st =
  let go = ref true in
  while !go do
    skip_ws st;
    skip_comment st;
    match peek st with
    | Some '\n' -> adv st
    | Some '\r' when peek_at st 1 = Some '\n' -> adv st
    | _ -> go := false
  done

let end_of_line st =
  skip_ws st;
  skip_comment st;
  match peek st with
  | None -> ()
  | Some '\n' -> adv st
  | Some '\r' when peek_at st 1 = Some '\n' ->
      adv st;
      adv st
  | Some c -> fail st.line "unexpected %C after a value" c

let utf8 buf code =
  let add c = Buffer.add_char buf (Char.chr c) in
  if code < 0x80 then add code
  else if code < 0x800 then (
    add (0xC0 lor (code lsr 6));
    add (0x80 lor (code land 0x3F)))
  else if code < 0x10000 then (
    add (0xE0 lor (code lsr 12));
    add (0x80 lor ((code lsr 6) land 0x3F));
    add (0x80 lor (code land 0x3F)))
  else (
    add (0xF0 lor (code lsr 18));
    add (0x80 lor ((code lsr 12) land 0x3F));
    add (0x80 lor ((code lsr 6) land 0x3F));
    add (0x80 lor (code land 0x3F)))

let escape st buf =
  adv st;
  match peek st with
  | Some 'b' -> adv st; Buffer.add_char buf '\b'
  | Some 't' -> adv st; Buffer.add_char buf '\t'
  | Some 'n' -> adv st; Buffer.add_char buf '\n'
  | Some 'f' -> adv st; Buffer.add_char buf '\012'
  | Some 'r' -> adv st; Buffer.add_char buf '\r'
  | Some '"' -> adv st; Buffer.add_char buf '"'
  | Some '\\' -> adv st; Buffer.add_char buf '\\'
  | Some (('u' | 'U') as c) ->
      adv st;
      let n = if c = 'u' then 4 else 8 in
      if st.i + n > String.length st.s then fail st.line "short \\%c escape" c;
      let hex = String.sub st.s st.i n in
      (match int_of_string_opt ("0x" ^ hex) with
      | Some code -> utf8 buf code
      | None -> fail st.line "bad \\%c escape" c);
      for _ = 1 to n do adv st done
  | _ -> fail st.line "bad escape"

let basic_string st =
  adv st;
  let buf = Buffer.create 16 in
  let rec go () =
    match peek st with
    | Some '"' -> adv st
    | Some '\\' -> escape st buf; go ()
    | Some '\n' | None -> fail st.line "unterminated string"
    | Some c -> adv st; Buffer.add_char buf c; go ()
  in
  go ();
  Buffer.contents buf

let literal_string st =
  adv st;
  let b = st.i in
  while match peek st with Some '\'' | Some '\n' | None -> false | _ -> true do
    adv st
  done;
  if peek st <> Some '\'' then fail st.line "unterminated string";
  let s = String.sub st.s b (st.i - b) in
  adv st;
  s

(* a newline straight after the opening delimiter is trimmed; up to two
   quotes may end the body just before the closing three *)
let multiline st ~basic =
  let q = if basic then "\"\"\"" else "'''" in
  for _ = 1 to 3 do adv st done;
  if peek st = Some '\n' then adv st
  else if peek st = Some '\r' && peek_at st 1 = Some '\n' then (adv st; adv st);
  let buf = Buffer.create 64 in
  let rec go () =
    if starts st q then (
      for _ = 1 to 3 do adv st done;
      let extra = ref 0 in
      while !extra < 2 && peek st = Some q.[0] do
        Buffer.add_char buf q.[0];
        adv st;
        incr extra
      done)
    else
      match peek st with
      | None -> fail st.line "unterminated string"
      | Some '\\' when basic ->
          (* a line-ending backslash eats the newline and following blanks *)
          let j = ref (st.i + 1) in
          while
            !j < String.length st.s && (st.s.[!j] = ' ' || st.s.[!j] = '\t')
          do
            incr j
          done;
          if !j < String.length st.s && (st.s.[!j] = '\n' || st.s.[!j] = '\r')
          then (
            while
              match peek st with
              | Some (' ' | '\t' | '\n' | '\r' | '\\') -> true
              | _ -> false
            do
              adv st
            done;
            go ())
          else (escape st buf; go ())
      | Some c -> adv st; Buffer.add_char buf c; go ()
  in
  go ();
  Buffer.contents buf

let is_bare c =
  match c with
  | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' | '-' -> true
  | _ -> false

let simple_key st =
  match peek st with
  | Some '"' -> basic_string st
  | Some '\'' -> literal_string st
  | Some c when is_bare c ->
      let b = st.i in
      while match peek st with Some c -> is_bare c | None -> false do
        adv st
      done;
      String.sub st.s b (st.i - b)
  | _ -> fail st.line "expected a key"

let key st =
  let rec go acc =
    skip_ws st;
    let k = simple_key st in
    skip_ws st;
    if peek st = Some '.' then (adv st; go (k :: acc)) else List.rev (k :: acc)
  in
  go []

(* numbers, booleans and date-times are one run of the characters any of
   them may contain, classified once whole *)
let scalar st =
  let b = st.i in
  let ok c =
    match c with
    | '0' .. '9' | 'a' .. 'z' | 'A' .. 'Z' | '_' | '+' | '-' | '.' | ':' -> true
    | ' ' ->
        (* a date and a time may be separated by one space *)
        st.i > b
        && (match peek_at st 1 with Some '0' .. '9' -> true | _ -> false)
        && st.i - b = 10
        && st.s.[b + 4] = '-'
    | _ -> false
  in
  while match peek st with Some c -> ok c | None -> false do
    adv st
  done;
  let w = String.sub st.s b (st.i - b) in
  let digits = String.concat "" (String.split_on_char '_' w) in
  match w with
  | "" -> fail st.line "expected a value"
  | "true" -> Bool true
  | "false" -> Bool false
  | "inf" | "+inf" -> Float infinity
  | "-inf" -> Float neg_infinity
  | "nan" | "+nan" | "-nan" -> Float nan
  | _ when (String.length w >= 10 && w.[4] = '-')
           || (String.length w >= 8 && w.[2] = ':') ->
      Date w
  | _ -> (
      match int_of_string_opt digits with
      | Some n -> Int n
      | None -> (
          match float_of_string_opt digits with
          | Some f -> Float f
          | None -> fail st.line "bad value %S" w))

let new_tbl explicit = { fields = []; explicit }

let rec value st =
  match peek st with
  | Some '"' ->
      if starts st "\"\"\"" then Str (multiline st ~basic:true)
      else Str (basic_string st)
  | Some '\'' ->
      if starts st "'''" then Str (multiline st ~basic:false)
      else Str (literal_string st)
  | Some '[' ->
      adv st;
      let rec go acc =
        skip_blank st;
        match peek st with
        | Some ']' -> adv st; Arr (List.rev acc)
        | _ -> (
            let v = value st in
            skip_blank st;
            match peek st with
            | Some ',' -> adv st; go (v :: acc)
            | Some ']' -> adv st; Arr (List.rev (v :: acc))
            | _ -> fail st.line "expected , or ] in an array")
      in
      go []
  | Some '{' ->
      adv st;
      let t = new_tbl true in
      (* newlines, comments and a trailing comma are TOML 1.1's; taking
         them reads no TOML 1.0 table differently *)
      let rec go () =
        skip_blank st;
        if peek st = Some '}' then adv st
        else begin
          let k = key st in
          if peek st <> Some '=' then fail st.line "expected =";
          adv st;
          skip_ws st;
          assign st t k (value st);
          skip_blank st;
          match peek st with
          | Some ',' -> adv st; go ()
          | Some '}' -> adv st
          | _ -> fail st.line "expected , or } in an inline table"
        end
      in
      go ();
      Tbl t
  | _ -> scalar st

(* a dotted key's leading parts are tables, made on the way if absent *)
and descend st (t : tbl) (k : string) : tbl =
  match List.assoc_opt k t.fields with
  | None ->
      let n = new_tbl false in
      t.fields <- t.fields @ [ (k, Tbl n) ];
      n
  | Some (Tbl n) -> n
  | Some (ATbl l) -> (
      match List.rev !l with n :: _ -> n | [] -> fail st.line "empty array")
  | Some _ -> fail st.line "key %S is not a table" k

and assign st (t : tbl) (ks : string list) (v : t) =
  match ks with
  | [] -> assert false
  | [ k ] ->
      if List.mem_assoc k t.fields then fail st.line "duplicate key %S" k;
      t.fields <- t.fields @ [ (k, v) ]
  | k :: rest -> assign st (descend st t k) rest v

let parse (s : string) : tbl =
  let st = { s; i = 0; line = 1 } in
  let root = new_tbl true in
  let cur = ref root in
  let rec loop () =
    skip_blank st;
    match peek st with
    | None -> ()
    | Some '[' ->
        let aot = peek_at st 1 = Some '[' in
        adv st;
        if aot then adv st;
        let ks = key st in
        if not (starts st (if aot then "]]" else "]")) then
          fail st.line "unterminated table header";
        adv st;
        if aot then adv st;
        end_of_line st;
        let rec parent t = function
          | [] | [ _ ] -> t
          | k :: rest -> parent (descend st t k) rest
        in
        let last = List.nth ks (List.length ks - 1) in
        let p = parent root ks in
        (if aot then (
           let n = new_tbl true in
           match List.assoc_opt last p.fields with
           | None -> p.fields <- p.fields @ [ (last, ATbl (ref [ n ])) ]; cur := n
           | Some (ATbl l) -> l := !l @ [ n ]; cur := n
           | Some _ -> fail st.line "%S is not an array of tables" last)
         else
           match List.assoc_opt last p.fields with
           | None ->
               let n = new_tbl true in
               p.fields <- p.fields @ [ (last, Tbl n) ];
               cur := n
           | Some (Tbl n) when not n.explicit ->
               n.explicit <- true;
               cur := n
           | Some _ -> fail st.line "table %S defined twice" (String.concat "." ks));
        loop ()
    | Some _ ->
        let ks = key st in
        if peek st <> Some '=' then fail st.line "expected =";
        adv st;
        skip_ws st;
        assign st !cur ks (value st);
        end_of_line st;
        loop ()
  in
  loop ();
  root

let of_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  parse s
