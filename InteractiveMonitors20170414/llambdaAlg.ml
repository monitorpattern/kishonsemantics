(** ----------------------------------------------------------------
    Semantic Algebras of the Llambda language
    ----------------------------------------------------------------
    Note: 'a is the Answer's type, "instantiated" with the initial
    continuation.
    When the semantics is parameterized with a monitor, 
    'a becomes 'm -> ('a Ans * 'm), 
    where 'm is the type of a monitor state.
    ------------------------------------------------------------------ *)
(* Basic values Bas *)
type basv = [ `Int of int | `Bool of bool | `List of int list ] (* or basv list *)
(* Function values Fun *)
type  'a funv = 'a denval -> 'a kont -> 'a ans
(* Denotable values V *)
and  'a denval = [ basv | `Fun of 'a funv ]
(* Answers Ans *)
(* TODO: and  'a ans = Ans of ('a -> in_channel -> (in_channel * out_channel)) *)
and  'a ans = Ans of 'a 
(* Environments Env *)
and  'a env = Env of (string -> 'a denval)
(* Expression continuations Kont *)
and  'a kont = 'a denval -> 'a ans

(* Store update *)
let update_rho i x = function Env rho ->
  Env (fun j -> if i = j then x else rho j)
let access_rho i = function Env rho -> rho i


(** ----------------------------------------------------------------
    DEPR COMMENT [Interactive debugging] Semantic Algebras
    ---------------------------------------------------------------- *)

(* ---------------------------  Handlers for interactive interpreter *)
module IO =
struct 
  type inChannel = string
  type outChannel = string
  let concat (s1:outChannel) (s2:outChannel) = String.concat "" [s1;s2]
  let concatList l = String.concat "" l
  let emptyIn = ""
  let emptyOut = ""
  let isEmpty s = s = "" 
  (* FIXME-HACK: do not split substrings protected by parenthesis e.g. (fac 0) *)
 let splitDebug str =
    let lst = Str.split(Str.regexp " +") str in
    let rec funl l acc b = match l with
      | [] -> acc
      | x::xs when (String.get x 0 = '(') ->
        funl xs (x::acc) true
      | x::xs when (String.get x ((String.length x) - 1) = ')') ->
        let r'::acc' = acc in 
        funl xs (acc'@[ String.concat " " [r';x] ]) false
      | x::xs ->
        if b = false then 
          funl xs (acc@[x]) b
        else
          let r'::acc' = acc in 
          funl xs ((String.concat " " [r';x])::acc') b
    in funl lst [] false     
  let split str =
    let lst = splitDebug str in
    match lst with 
      | [] -> "",""
      | x::xs -> x, (String.concat " " xs)
end

  
(** ----------------------------------------------------------------
    Pretty printing functions
    ---------------------------------------------------------------- *)
  
let string_of_denval = function
  | `Int  i -> string_of_int i
  | `Bool b -> string_of_bool b
  | `List l -> String.concat ";" (List.map string_of_int l)
  | `Fun f -> "a function..."

let string_of_basv = function
  | `Int  i -> string_of_int i
  | `Bool b -> string_of_bool b
  | `List l -> String.concat ";" (List.map string_of_int l)

let basv_of_denval = function
  | `Int  i -> `Int  i
  | `Bool b -> `Bool b
  | `List l -> `List l
  | `Fun f -> failwith "Not a base value"
