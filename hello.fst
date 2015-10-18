(*--build-config
options:--n_cores 2 --max_fuel 2 --admit_fsi FStar.Set --admit_fsi FStar.Heap --admit_fsi FStar.ST --admit_fsi FStar.All --admit_fsi FStar.IO;
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

val hdcons : 'a -> xss:list (list 'a){xss<>[]} -> yss:list (list 'a){yss<>[]}
let hdcons x xss = (x::hd xss)::tl xss

val listSplit : ('a -> Tot bool) -> list 'a -> Tot (yss:list (list 'a){yss<>[]})
let rec listSplit p xs' = match xs' with
  | [] -> [[]]
  | x::xs -> let yss = listSplit p xs in
    if p x then
      [x]::yss
    else
      hdcons x yss

val isLineBreak : editorChar -> Tot bool
let isLineBreak (ch,_) = (ch = '\n')

val listLines : list editorChar -> Tot (list (list editorChar))
let listLines es = listSplit isLineBreak es

val annotate : list char -> int -> Tot (list editorChar)
let rec annotate cs' n = match cs' with
  | [] -> []
  | c::cs -> (c,n=0)::annotate cs (n-1)

val buffer_annotate : buffer -> Tot (list editorChar)
let buffer_annotate (w,h,pos,str) = annotate str pos

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

val buffer_lines : buffer -> Tot (list (list editorChar))
let buffer_lines buf = listLines (buffer_annotate buf)

val buffer_w : buffer -> Tot nat
let buffer_w (w, _, _, _) = w

val buffer_h : buffer -> Tot nat
let buffer_h (_, h, _, _) = h

val buffer_pos : buffer -> Tot nat
let buffer_pos (_, _, pos, _) = pos

val buffer_cs : buffer -> Tot (list char)
let buffer_cs (_, _, _, cs) = cs

val buffer_padded_lines : buffer -> Tot (list (list editorChar))
let buffer_padded_lines buf = map (fun line -> pad_line (buffer_w buf) line) (buffer_lines buf)

val display_buffer : buffer -> Tot terminalScreen
let display_buffer buf =
  let w = buffer_w buf in
  let h = buffer_h buf in
  let padded_lines = buffer_padded_lines buf in
  let empty_line = pad_line w [] in
  let egrid = pad_list h empty_line padded_lines in
  let grid = scrubCursor egrid in
  let (cx,cy) = findCursorOrZero egrid in
  Screen w h cx cy grid

val state : ref buffer
let state = ST.alloc (80,25,0,[])

val list_insert : nat -> 'a -> list 'a -> Tot (list 'a)
let rec list_insert i y xs' =
  match i with
  | 0 -> y::xs'
  | _ -> match xs' with
    | [] -> [y]
    | x::xs -> x::list_insert (i-1) y xs

type buffer_changer b =
  p:(buffer * list char){Some (display_buffer (fst p)) = screen_advance (snd p) (display_buffer b)}
//type buffer_changer (b:buffer) = (buffer * list char)

val noop : b:buffer -> Tot (buffer_changer b)
let noop buf = (buf,[])

val buffer_insert : char -> buffer -> Tot buffer
let buffer_insert ch (w,h,i,chars) =
  let chars' = list_insert i ch chars in
  (w,h,i+1,chars')

(* The effect that inserting a character has on annotate *)
val annotate_ins_empty : n:nat -> ch:char -> Lemma (annotate (list_insert n ch []) (n+1) = list_insert n (ch,false) (annotate [] n))
let annotate_ins_empty n ch = ()

val annotate_ins :
  n:nat -> cs:list char -> ch:char ->
  Lemma (annotate (list_insert n ch cs) (n+1)
    = list_insert n (ch,false) (annotate cs n))
let rec annotate_ins n cs' ch =
  match cs' with
  | [] -> annotate_ins_empty n ch
  | c::cs -> match n with
    | 0 -> ()
    | _ -> annotate_ins (n-1) cs ch

val buffer_annotate_ins :
  b:buffer -> ch:char ->
  Lemma (buffer_annotate (buffer_insert ch b)
    = list_insert (buffer_pos b) (ch,false) (buffer_annotate b))
let buffer_annotate_ins b ch
  = annotate_ins (buffer_pos b) (buffer_cs b) ch

val grow_char : char -> editorChar -> Tot (list editorChar)
let grow_char ch (c,cursor) = if cursor then [(ch,false);(c,cursor)] else [(c,cursor)]

val line_insert : char -> list editorChar -> Tot (list editorChar)
let line_insert ch es = concatMap (grow_char ch) es

val lines_insert : char -> list (list editorChar) -> Tot (list (list editorChar))
let lines_insert ch b = map (line_insert ch) b

(* The effect of inserting a character into appended lines *)
val line_ins_append : ch:char -> es:list editorChar -> ess:list (list editorChar) ->
  Lemma (lines_insert ch (es::ess) = line_insert ch es::lines_insert ch ess)
let line_ins_append ch es ess = ()

(*
val has_no_linebreaks : list editorChar -> Tot bool
let rec has_no_linebreaks es' = match es' with
  | [] -> true
  | e::es -> not(isLineBreak e) && has_no_linebreaks es

val only_has_linebreak_at_end : list editorChar -> Tot bool
let rec only_has_linebreak_at_end es' = match es' with
  | [] -> false
  | [e] -> isLineBreak e
  | e::f::es -> not(isLineBreak e) && only_has_linebreak_at_end (f::es)

val grow_no_linebreaks : ch:char{ch<>'\n'} -> e:editorChar{not(isLineBreak e)} ->
  Lemma (has_no_linebreaks (grow_char ch e))
let grow_no_linebreaks ch (c,b) =
  if b then (
    assert(grow_char ch (c,b) = [(ch,false);(c,b)]);
    assert(has_no_linebreaks [(c,b)]);
    assert(not(isLineBreak((ch,false))));
    assert(has_no_linebreaks([(ch,false);(c,b)]));
    ()
  ) else (
    assert(grow_char ch (c,b) = [(c,b)]);
    ()
  )
  
val grow_only_linebreak_at_end : ch:char{ch<>'\n'} -> e:editorChar{isLineBreak e} ->
  Lemma (only_has_linebreak_at_end (grow_char ch e))
let grow_only_linebreak_at_end ch (c,b) =
  if b then (
    assert(grow_char ch (c,b) = [(ch,false);(c,b)]);
    ()
  ) else (
    assert(grow_char ch (c,b) = [(c,b)]);
    ()
  )

(* Appending a has_no_linebreaks *)
val appending_no_linebreaks : es:list editorChar{has_no_linebreaks es} -> fs:list editorChar ->
  Lemma (listLines (es @@ fs) = (es @@ hd (listLines fs)) :: tl (listLines fs))
let rec appending_no_linebreaks es' fs =
  match es' with
    | [] -> ()
    | (e::es) ->
      assert(not(isLineBreak e));
      //assert listLines ((e::es)@fs) = (e::hd (listLines (es@@fs)))::tl (listLines (es@@fs))
      appending_no_linebreaks es fs;
      ()

(* Appending only_has_linebreak_at_end *)
val appending_only_linebreak_at_end : es:list editorChar{only_has_linebreak_at_end es} -> fs:list editorChar ->
  Lemma (listLines (es @@ fs) = es :: listLines fs)
let rec appending_only_linebreak_at_end es' fs =
  match es' with
    | [] -> assert(false)
    | [e] ->
      assert(isLineBreak e);
      ()
    | e::e'::es ->
      assert(not(isLineBreak e));
      appending_only_linebreak_at_end (e'::es) fs;
      ()
*)

val listLines_cons : e:editorChar{~isLineBreak e} -> es:list editorChar ->
  Lemma (listLines (e::es) = hdcons e (listLines es))
let listLines_cons e es = ()

val lines_ins_linebreak : e:editorChar{isLineBreak e} -> es:list editorChar -> ch:char{isPrintableChar ch} ->
  Lemma (listLines (line_insert ch (e::es)) = lines_insert ch (listLines (e::es)))
let lines_ins_linebreak :
	assert(not(isLineBreak (ch,false)));
	assert(isLineBreak e);
	grow_only_linebreak_at_end ch e;
        assert(only_has_linebreak_at_end (grow_char ch e));
	lines_ins es ch;
	line_ins_append ch [e] (listLines es);
        assert(line_insert ch (e::es) = (grow_char ch e @@ line_insert ch es));
	appending_only_linebreak_at_end (grow_char ch e) (line_insert ch es);
	assert(listLines (line_insert ch (e::es)) = listLines (grow_char ch e @@ line_insert ch es));
	assert(listLines (line_insert ch (e::es)) = lines_insert ch (listLines (e::es)));
	assert(listLines (line_insert ch es') = lines_insert ch (listLines es'))

(* The effect that inserting a character has on lines *)
val lines_ins : es:list editorChar -> ch:char{isPrintableChar ch} ->
  Lemma (listLines (line_insert ch es) = lines_insert ch (listLines es))
let rec lines_ins es' ch =
  (match es' with
    | [] -> ()
    | e::es ->
      if isLineBreak e then (
      ) else (
	assert(not(isLineBreak (ch,false)));
	assert(not(isLineBreak e));
	grow_no_linebreaks ch e;
        assert(has_no_linebreaks (grow_char ch e));
        lines_ins es ch;
	line_ins_append ch (e::hd (listLines es)) (tl (listLines es));
	appending_no_linebreaks (grow_char ch e) (line_insert ch es);
	assert(listLines (line_insert ch (e::es)) = lines_insert ch (listLines (e::es)));
	assert(listLines (line_insert ch es') = lines_insert ch (listLines es'))
      );
      assert(listLines (line_insert ch es') = lines_insert ch (listLines es'))
  );
  assert(listLines (line_insert ch es') = lines_insert ch (listLines es'))
  
val line_insert_annotate_negative : es:list char -> n:int{n<0} -> ch:char ->
  Lemma (line_insert ch (annotate es n) = annotate es n)
let rec line_insert_annotate_negative es' n ch = match es' with
  | [] -> ()
  | e::es -> line_insert_annotate_negative es (n-1) ch

val list_insert_line_insert0 : c:char -> cs:list char -> ch:char ->
  Lemma (list_insert 0 (ch,false) (annotate (c::cs) 0) = line_insert ch (annotate (c::cs) 0))
let list_insert_line_insert0 c cs ch =
      assert(list_insert 0 (ch,false) (annotate (c::cs) 0) = (ch,false)::annotate (c::cs) 0);
      assert(annotate (c::cs) 0 = (c,true)::annotate cs (-1));
      line_insert_annotate_negative cs (-1) ch;
      assert(line_insert ch (annotate (c::cs) 0) = (ch,false)::annotate (c::cs) 0);
      ()

val list_insert_line_insert' : es:list char -> n:nat -> ch:char ->
  Lemma (list_insert n (ch,false) (annotate es n) = line_insert ch (annotate es n))
let rec list_insert_line_insert' es' n ch
  = match es' with
  | [] -> ()
  | e::es ->
    match n with
    | 0 ->
       list_insert_line_insert0 e es ch
    | _ ->
      list_insert_line_insert' es (n-1) ch;
      assert(list_insert n (ch,false) (annotate es' n) = line_insert ch (annotate es' n));
      ()

(*val list_insert_line_insert : b:buffer -> ch:char ->
  Lemma (list_insert (buffer_pos b) (ch,false) (buffer_annotate b) = line_insert ch (buffer_annotate b))
let rec list_insert_line_insert (w,h,pos,cs') ch
  = match cs' with
  | [] -> ()
  | c::cs ->
      match pos with
      | 0 ->
	assert(buffer_annotate (w,h,pos,cs') = *)

val buffer_lines_ins : b:buffer -> ch:char{isPrintableChar ch} ->
  Lemma (buffer_lines (buffer_insert ch b) = lines_insert ch (buffer_lines b))
let buffer_lines_ins b ch =
  assert(buffer_lines (buffer_insert ch b) = listLines (buffer_annotate (buffer_insert ch b)));
  buffer_annotate_ins b ch;
  list_insert_line_insert' (buffer_cs b) (buffer_pos b) ch;
  assert (list_insert (buffer_pos b) (ch,false) (buffer_annotate b) = line_insert ch (buffer_annotate b));
  assert(buffer_annotate (buffer_insert ch b) = line_insert ch (buffer_annotate b));
  lines_ins (buffer_annotate b) ch

(* The effect that inserting a character has on display_buffer *)
val buffer_inserting_character :
  b:buffer -> ch:char{isPrintableChar ch} ->
  Lemma (display_buffer (buffer_insert ch b)
    = screenInsertChar ch (display_buffer b))
let buffer_inserting_character b ch = buffer_annotate_ins b ch

val insert_char : char -> b:buffer -> Tot (buffer_changer b)
let insert_char ch buf =
  let buf' = buffer_insert ch buf in
  let output = esc::'['::'@'::ch::[] in
  buffer_inserting_character buf ch;
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
