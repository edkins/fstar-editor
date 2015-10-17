(*--build-config
options:--admit_fsi FStar.Set;
other-files:set.fsi heap.fst st.fst all.fst io.fsti string.fst list.fst char.fst;
--*)
module Terminal

open FStar.List
open FStar.Char

(*
type vector : Type -> nat -> Type =
   | Nil :  vector 'a 0
   | Cons : hd:'a -> n:nat -> tl:vector 'a n -> vector 'a (n + 1)
   
*)

type vector 't (n:nat) : Type = x:list 't{length x = n}

val vtail : (n:nat) -> vector 't (n+1) -> Tot (vector 't n)
let vtail n (x::xs) = xs

val vnth : (n:nat) -> vector 't n -> i:nat{i<n} -> Tot 't
let rec vnth n (x::xs) i =
  match i with
  | 0 -> x
  | _ -> vnth (n-1) xs (i-1)

val vmod : (n:nat) -> i:nat{i<n} -> ('t -> Tot 't) -> vector 't n -> Tot (vector 't n)
let rec vmod n i f (x::xs) =
  match i with
  | 0 -> f x::xs
  | _ -> x :: vmod (n-1) (i-1) f xs

val vset : n:nat -> i:nat{i<n} -> 't -> vector 't n -> Tot (vector 't n)
let vset n i x v = vmod n i (fun _ -> x) v

type grid 't (w:nat) (h:nat) : Type = x:vector (list 't) h {forall (i:nat). i < h ==> length (vnth h x i) = w}
type grid2 't (w:nat) (h:nat) : Type = vector (vector 't w) h

val gridModRow : w:nat -> h:nat -> y:nat{y<h} -> (vector 't w -> Tot (vector 't w)) -> grid2 't w h -> Tot (grid2 't w h)
let gridModRow w h y f g = vmod h y f g

val gridWith : w:nat -> h:nat -> x:nat{x<w} -> y:nat{y<h} -> 't -> grid2 't w h -> Tot (grid2 't w h)
let gridWith w h x y v g = vmod h y (vset w x v) g

type terminalState : Type =
  | StateDefault : terminalState
  | StateEscape : string -> terminalState

type terminalScreen : Type =
  | Screen :
      width:nat{width=80} ->
      height:nat{height=25} ->
      (cx:nat{cx<width}) ->
      (cy:nat{cy<height}) ->
//      xss:list (xs:list nat{length xs=width}){xss=[]} -> 
      xss:list (xs:list nat{length xs=width}){xss=[]} -> 
      terminalScreen

type terminal : Type = option (terminalState * terminalScreen)

val isPrintableChar : char -> Tot bool
let isPrintableChar ch =
  (int_of_char ch >= int_of_char ' ') && (int_of_char ch <= int_of_char '~')

val screenPrint : char -> terminalScreen -> Tot (option terminalScreen)
let screenPrint ch (Screen w h cx cy chars) =
  let chars' = gridWith w h cx cy ch chars in
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
