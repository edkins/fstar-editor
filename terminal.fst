(*--build-config
options:--admit_fsi FStar.Set;
other-files:set.fsi heap.fst st.fst all.fst io.fsti string.fst list.fst char.fst;
--*)
module Terminal

open FStar.List
open FStar.Char

val listmod : nat -> ('a -> Tot 'a) -> list 'a -> Tot (list 'a)
let rec listmod n f xs' = match xs' with
  | [] -> []
  | x::xs -> match n with
    | 0 -> f x::xs
    | _ -> x::listmod (n-1) f xs

val gridWith : nat -> nat -> 'a -> list (list 'a) -> Tot (list (list 'a))
let gridWith x y c g =
  listmod y (fun row -> listmod x (fun _->c) row) g

type terminalState : Type =
  | StateDefault : terminalState
  | StateEscape : string -> terminalState

type terminalScreen : Type =
  | Screen :
      width:nat ->
      height:nat ->
      cx:nat ->
      cy:nat ->
      list (list char) ->
      terminalScreen

type terminal : Type = option (terminalState * terminalScreen)

val isPrintableChar : char -> Tot bool
let isPrintableChar ch =
  (int_of_char ch >= int_of_char ' ') && (int_of_char ch <= int_of_char '~')

val screenPrint : char -> terminalScreen -> Tot (option terminalScreen)
let screenPrint ch (Screen w h cx cy chars) =
  let chars' = gridWith cx cy ch chars in
  if cx = w - 1 then
  (
    if cy = h - 1 then
      None
    else
      Some (Screen w h 0 (cy+1) chars')
  )
  else
    Some (Screen w h (cx+1) cy chars')

val screenNextLine : terminalScreen -> Tot (option terminalScreen)
let screenNextLine (Screen w h cx cy chars) =
  if cy = h - 1 then
    None
  else
    Some (Screen w h 0 (cy+1) chars)

val screenNop : terminalScreen -> Tot (option terminalScreen)
let screenNop screen = Some screen

val screenError : terminalScreen -> Tot (option terminalScreen)
let screenError screen = None

val termCharAction : char -> terminalState -> Tot ((terminalScreen -> Tot (option terminalScreen)) * terminalState)
let termCharAction ch state =
  if isPrintableChar ch && state = StateDefault then
    (screenPrint ch, StateDefault)
  else if ch = '\n' && state = StateDefault then
    (screenNextLine, StateDefault)
  else if ch = '\n' && state = StateDefault then
    (screenNop, StateEscape "")
  else
    (screenError, StateDefault)

val termChar : char -> terminal -> Tot terminal
let termChar ch term =
  match term with
  | Some (state, screen) ->
    let (f, state') = termCharAction ch state in
    (
    match f screen with
      | Some screen' -> Some (state', screen')
      | None -> None
    )
  | None -> None
