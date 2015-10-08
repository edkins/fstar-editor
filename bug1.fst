module Hello
open FStar.IO
open FStar.ST

let state = ST.alloc 0

(*
Uncommenting the following line changes the behaviour of the program
*)

//val editor : unit -> ML unit
let rec editor () =
  print_int !state;
  editor ()
;;
   
editor ()


