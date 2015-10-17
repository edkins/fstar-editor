(*--build-config
options:--admit_fsi FStar.Set;
other-files:set.fsi heap.fst st.fst all.fst io.fsti string.fst listTot.fst char.fst;
--*)
module Terminal

open FStar.List.Tot
open FStar.Char
open FStar.String

let op_At_At (xs:list 'a) (ys:list 'a) = append xs ys

val charsstr : list char -> Tot string
let charsstr cs = fold_right (fun c str -> strcat str (make 1 c)) cs ""

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
  | StateEscape : list char -> terminalState

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

val esc : char
let esc = char_of_byte 27

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

val init : list 'a -> Tot (list 'a)
let rec init xs' = match xs' with
  | [] -> []
  | [x] -> []
  | x::xs -> x::init xs

val listins : list 'a -> nat -> 'a -> Tot (list 'a)
let rec listins xs' n y = match xs' with
  | [] -> []
  | x::xs -> match n with
    | 0 -> y::init xs'
    | _ -> x::listins xs (n-1) y

val screenInsertChar : char -> terminalScreen -> Tot (option terminalScreen)
let screenInsertChar ch (Screen w h cx cy chars) =
  let chars' = listmod cy (fun row -> listins row cx ch) chars in
  Some (Screen w h cx cy chars')

val screenDoEscape : list char -> terminalScreen -> Tot (option terminalScreen)
let screenDoEscape str screen =
  match charsstr str with
    | "[@" -> screenInsertChar ' ' screen
    | _ -> None

val endsEscape : char -> Tot bool
let endsEscape ch = (int_of_char ch >= int_of_char '@') && (int_of_char ch <= int_of_char 'Z')

val termCharAction : char -> terminalState -> Tot ((terminalScreen -> Tot (option terminalScreen)) * terminalState)
let termCharAction ch state =
  match state with
    | StateDefault ->
      if isPrintableChar ch && state = StateDefault then
        (screenPrint ch, StateDefault)
      else if ch = '\n' && state = StateDefault then
        (screenNextLine, StateDefault)
      else if ch = esc && state = StateDefault then
        (screenNop, StateEscape [])
      else
        (screenError, StateDefault)
    | StateEscape str ->
       if endsEscape ch then
         (screenDoEscape (str @@ [ch]), StateDefault)
       else
	 (screenNop, StateEscape (str @@ [ch]))

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

val weaken : n:nat -> m:nat{m<n} -> Tot (m':nat{m'<n+1})
let weaken _ m = m

val countUpTo : m:nat -> Tot (list (k:nat{k<m}))
let rec countUpTo n = match n with
  | 0 -> []
  | _ -> map (weaken (n-1)) (countUpTo (n-1)) @@ [n-1]

val strchars : string -> Tot (list char)
let strchars str = map (fun i -> getTot str i) (countUpTo (strlen str))

val termString : string -> terminal -> Tot terminal
let termString str term =
  fold_right termChar (strchars str) term

val termChars : list char -> terminal -> Tot terminal
let termChars cs term = fold_right termChar cs term
