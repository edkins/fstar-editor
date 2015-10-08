module Hello
open FStar.IO
open FStar.ST

let state = ST.alloc 0

val editor : unit -> ML unit
let rec editor () =
  print_int !state;
  let ch = input_char () in
  (if ch = 'a' then
    state := !state + 1
  else
    state := !state - 1);
  editor ()
;;
   
editor ()


