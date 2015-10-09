module Hello
open FStar.IO
open FStar.ST
open FStar.String
open FStar.List

val buffer : ref (list (ref string))
let buffer = ST.alloc [ST.alloc ""]
let cursor_row = ST.alloc 0
let cursor_col = ST.alloc 0

val str_insert : int -> char -> string -> string
let str_insert i ch str = strcat (substring str 0 i) (strcat (make 1 ch) (substring str i (strlen str - i)))

val insert_char : char -> ML unit
let insert_char ch =
  let sref = nth !buffer !cursor_row in
  let str = str_insert !cursor_col ch !sref in
  sref := str

val print_lines : list (ref string) -> ML unit
let rec print_lines rs' = match rs' with
  | [] -> ()
  | (r::rs) -> print_string !r; print_string "\n"; print_lines rs

val print_buffer : unit -> ML unit
let print_buffer () =
  print_lines !buffer

val handle_key : char -> ML unit
let handle_key ch =
  insert_char ch

val editor : unit -> ML unit
let rec editor () =
  let ch = input_char () in
  handle_key ch;
  print_buffer ();
  editor ()
;;
   
editor ()
