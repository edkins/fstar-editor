(*--build-config
options:--admit_fsi FStar.Set --admit_fsi FStar.Heap --admit_fsi FStar.ST --admit_fsi FStar.All --admit_fsi FStar.IO;
other-files:set.fsi heap.fst st.fst all.fst io.fsti string.fst listTot.fst char.fst terminal.fst;
--*)
module Hello
open FStar.IO
open FStar.ST
open FStar.String
open FStar.List.Tot
open Terminal

type buffer = (nat * nat * nat * list char)

val screen_advance : list char -> terminalScreen -> Tot (option terminalScreen)
let screen_advance cs scr =
  let term = Some (StateDefault, scr) in
  match termChars cs term with
  | None -> None
  | Some (state, scr') ->
    if state = StateDefault then Some scr' else None

val pad_list : nat -> 'a -> list 'a -> Tot (list 'a)
let rec pad_list n v xs' = match n with
  | 0 -> []
  | _ -> match xs' with
    | [] -> v :: pad_list (n-1) v []
    | x::xs -> x :: pad_list (n-1) v xs

type editorChar = (char * bool)

val pad_line : nat -> list editorChar -> Tot (list editorChar)
let pad_line n cs = pad_list n (' ',false) cs

val isLineBreak : editorChar -> Tot bool
let isLineBreak (ch,_) = (ch = '\n')

val listLines : list editorChar -> Tot (list editorChar * list (list editorChar))
let rec listLines cs' = match cs' with
  | [] -> ([],[])
  | c::cs -> let (line,lines) = listLines cs in
    if isLineBreak c then
      ([c], line :: lines)
    else
      (c::line, lines)

val annotate : list char -> int -> Tot (list editorChar)
let rec annotate cs' n = match cs' with
  | [] -> []
  | c::cs -> (c,n=0)::annotate cs (n-1)

val scrubCursor : list (list editorChar) -> Tot (list (list char))
let scrubCursor = map (map fst)

val findCursorRow : list editorChar -> Tot (option nat)
let rec findCursorRow es' = match es' with
  | [] -> None
  | (_,c)::es -> if c then Some 0 else
    match (findCursorRow es) with
      | None -> None
      | Some n -> Some (n+1)

val findCursor : list (list editorChar) -> Tot (option (nat * nat))
let rec findCursor ess' = match ess' with
  | [] -> None
  | es::ess -> match findCursorRow es with
    | Some n -> Some (0,n)
    | None -> match findCursor ess with
      | None -> None
      | Some (m,n) -> Some (m+1,n)

val findCursorOrZero : list (list editorChar) -> Tot (nat * nat)
let findCursorOrZero ess = match findCursor ess with
  | None -> (0,0)
  | Some (m,n) -> (m,n)

val display_buffer : buffer -> Tot terminalScreen
let display_buffer (w, h, pos, bufstr) =
  let echars = annotate bufstr pos in
  let (line,lines) = listLines echars in
  let lines' = line::lines in
  let padded_lines = map (fun line -> pad_line w line) lines' in
  let empty_line = pad_line w [] in
  let egrid = pad_list h empty_line padded_lines in
  let grid = scrubCursor egrid in
  let (cx,cy) = findCursorOrZero egrid in
  Screen w h cx cy grid

type buffer_changer b =
  p:(buffer * list char){Some (display_buffer (fst p)) = screen_advance (snd p) (display_buffer b)}
//type buffer_changer (b:buffer) = (buffer * list char)

//val l_screen_advance_empty : (s:terminalScreen) -> Lemma (screen_advance [] s = Some s)
//let l_screen_advance_empty b = ()

val state : ref buffer
let state = ST.alloc (80,25,0,[])

val noop : b:buffer -> Tot (buffer_changer b)
let noop buf = (buf,[])

val list_insert : nat -> 'a -> list 'a -> Tot (list 'a)
let rec list_insert i y xs' =
  match i with
  | 0 -> y::xs'
  | _ -> match xs' with
    | [] -> [y]
    | x::xs -> x::list_insert (i-1) y xs

val insert_char : char -> b:buffer -> Tot (buffer_changer b)
let insert_char ch (w,h,i,chars) =
  let chars' = list_insert i ch chars in
  let buf' = (w,h,i+1,chars') in
  let output = esc::'['::'@'::ch::[] in
  (buf', output)

val handle_key : char -> b:buffer -> Tot (buffer_changer b)
let handle_key ch buf =
  if isPrintableChar ch then
    insert_char ch buf
  else
    noop buf

val editor : unit -> ML unit
let rec editor () =
  let (ch:char) = input_char () in
  let (s:buffer) = !state in
  let bch = handle_key ch s in
  let (state', cs) = bch in
  state := state';
  print_string (charsstr cs);
  editor ()
;;
   
editor ()
