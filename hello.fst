module Hello
open FStar.IO
open FStar.ST

let editor () =
  let x = ST.alloc 0 in
  x := !x + 1;
  print_int !x

let print_message x =
  print_string x

let ch = input_char ()
;;

(* The "main" expression is delimited
   from the rest of the module by ';;' *)
   
editor ()


