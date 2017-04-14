(** ----------------------------------------------------------------
 * Paper experiment: 
 *   Monitoring Semantics : A Formal framework for Specifying, Implementing,
 *   and Reasoning about Execution Monitors.
 * Standard continuation semantics (Fig. 2) And
 * Parameterized monitoring semantics (Fig. 3) *
 * ---------------------------------------------------------------- **)
open Fixpoint
(** ----------------------------------------------------------------
   Abstract Syntax
   ----------------------------------------------------------------
   Notes: 'm is the type of Monitor State, "instantiated" when a
   monitor function is attached to the language evaluator.
   ------------------------------------------------------------------ *)
type con = BOOL of bool | NAT of int | LIST of int list
type  id = string
type  'm ann = Ann of 'm

type  'm expr  = ..
type  'm expr +=
  | Unit (* To fake a letrec without arguments *)
  | Con of con
  | Id of id
  | Lam of id *  'm expr
  | Cond of  'm expr *  'm expr *  'm expr
  | App of  'm expr *  'm expr
  | Letrec of id * (id *  'm expr *  'm expr)
  | Let of id * 'm expr * 'm expr
  | Succ of  'm expr

(* "Primitive" 'm expressions *)
type 'm expr +=
  | Leq of  'm expr *  'm expr      
  | Eq of  'm expr *  'm expr
  | Plus of 'm expr * 'm expr
  | Minus of  'm expr *  'm expr
  | Mult of  'm expr *  'm expr
  | Div of 'm expr * 'm expr
  | Mod of 'm expr * 'm expr
(* Primitive list expressions *)
type 'm expr +=
  | Tail of id
  | Head of id
  | Cons of 'm expr * id  

type 'm expr += AnnExpr of 'm ann * 'm expr
let string_of_expr e =
  let rec string_of_expr = function
    | Unit -> "unit"
    | Con c -> (match c with BOOL b -> string_of_bool b | NAT i -> string_of_int i | LIST l -> "[" ^ String.concat ";"  (List.map string_of_int l) ^ "]")
    | Id i ->  i 
    | Lam (i, e) -> "lambda " ^ i ^ " . " ^ (string_of_expr e)
    | Cond (ec, e1,e2) -> (string_of_expr ec) ^ " -> " ^ (string_of_expr e1) ^ " [] " ^ (string_of_expr e2)
    | App (e1, e2) -> (string_of_expr e1) ^ " " ^ (string_of_expr e2) ^ " " 
    | Letrec (i , (i_arg, e1, e2)) -> "letrec " ^ i ^ " " ^ i_arg ^ " = "  ^ (string_of_expr e1) ^ " in\n" ^ (string_of_expr e2)
    | Let (i, e1, e2) -> "let "^i ^ " = " ^ (string_of_expr e1) ^ " in\n" ^ (string_of_expr e2)
    | Succ e -> "(" ^ (string_of_expr e) ^ " + 1)"
    | Leq (e1,e2) -> "(" ^ (string_of_expr e1) ^ " <= " ^ (string_of_expr e2) ^ ")"
    | Eq (e1,e2) -> "(" ^ (string_of_expr e1) ^ " = " ^ (string_of_expr e2)^ ")"
    | Plus (e1,e2) -> "(" ^ (string_of_expr e1) ^ " + " ^ (string_of_expr e2)^ ")"
    | Minus(e1,e2) -> "(" ^ (string_of_expr e1) ^ " - " ^ (string_of_expr e2)^ ")"
    | Mult(e1,e2) -> "(" ^ (string_of_expr e1) ^ " * " ^ (string_of_expr e2)^ ")"
    | Div(e1,e2) -> "(" ^ (string_of_expr e1) ^ " / " ^ (string_of_expr e2)^ ")"
    | Mod(e1,e2) -> "(" ^ (string_of_expr e1) ^ " mod " ^ (string_of_expr e2)^ ")"
    | Tail i -> "tail " ^ i
    | Head i -> "head " ^ i
    | Cons (e, i) -> " (" ^ (string_of_expr e) ^ ")::" ^ i
    | AnnExpr (a, e) -> "!:"^(string_of_expr e)
  in "\n" ^ (string_of_expr e)
    
(** ----------------------------------------------------------------
    Semantic Algebras
    ----------------------------------------------------------------
    Note: 'a is the type of Answer, "instantiated" with the initial
    continuation.
    When the semantics is parameterized with a monitor, 'a become 'm -> ('a Ans * 'm)
    ------------------------------------------------------------------ *)
(* Basic values Bas *)
type basv = [ `Int of int | `Bool of bool | `List of int list ] (* or basv list *)
(* Function values Fun *)
type  'a funv = 'a denval -> 'a kont -> 'a ans
(* Denotable values V *)
and  'a denval = [ basv | `Fun of 'a funv ]
(* Answers Ans *)
and  'a ans = Ans of 'a 
(* Environments Env *)
and  'a env = Env of (string -> 'a denval)
(* Expression continuations Kont *)
and  'a kont = 'a denval -> 'a ans

(* Store update *)
let update_rho i x = function Env rho ->
  Env (fun j -> if i = j then x else rho j)
let access_rho i = function Env rho -> rho i

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

    
(** ----------------------------------------------------------------
   Valuation functional
   ------------------------------------------------------------------ *)
  
(* type t_i = syntax_i -> arg*_i -> kont_i -> ans 
   with konti = arg*i -> ans *)
type ('a,'m) t_lambda =  'm expr -> 'a env -> 'a kont -> 'a ans

(* val kfun : con -> denval *)
let kfun = function BOOL b -> `Bool b | NAT n -> `Int n | LIST l -> `List l

(* Return the primitive operator (+,-,* ) of the given expression (to ease tests...) *)
let bool_of_expr e = match e with
  | Leq _ -> (<=) | Eq _ -> (=) | _ -> failwith "Invalid boolean-operator"

(* Return the primitive operator (+,-,* ) of the given expression *)
let prim_of_expr e = match e with
  | Minus _ -> (-) | Plus _ -> (+) | Mult _ -> ( * ) | Div _ -> (/) | Mod _ -> ( mod ) | _ -> failwith "Invalid primitive-operator"
    
(* chunk of the valuation functional that handles primitive operations *)
let g_lambda_primitive (valfun:('a,'m) t_lambda) e rho kont =
  match e with 
    | Eq (e1, e2) | Leq (e1, e2) ->
      valfun e1 rho (fun v1 ->
        valfun e2 rho (fun v2 -> kont (`Bool ((bool_of_expr e) v1 v2))))
    | Minus (e1, e2) | Plus (e1, e2) | Mult (e1, e2) | Div (e1, e2) | Mod (e1, e2) ->
      valfun e1 rho (fun (`Int v1) ->
        valfun e2 rho (fun (`Int v2) -> kont (`Int ((prim_of_expr e) v1 v2))))
    | Succ e' -> valfun e' rho (fun (`Int v) -> kont (`Int (v+1)))
    | Tail i -> (match access_rho i rho with | `List (x::l) -> kont (`List l) | _ -> failwith "Tail misusage")
    | Head i -> (match access_rho i rho with | `List (x::l) -> kont (`Int x)  | _ -> failwith "Head misusage")
    | Cons (e1, i) -> (match access_rho i rho with | `List l -> valfun e1 rho (fun (`Int v) -> kont (`List (v::l))) | _ -> failwith "Cons misusage")
        
(* g_lambda : ValuationFunction -> SyntaxExpression -> Environment -> Continuation -> 'a T_lambda
i.e. type ('a,'m) t_lambda g_lambda = 'a t_lambda -> 'a t_lambda *)
let g_lambda valfun e rho kont = match e with
  | Unit             ->  kont (kfun (NAT 0)) (* hack *)
  | Con k            -> kont (kfun k)
  | Id i  -> kont (access_rho i rho)
  | Lam (arg, ebody) ->  kont (`Fun (fun v kont' -> valfun ebody (update_rho arg v rho) kont'))
  | Cond (e1, e2, e3)-> valfun e1 rho (function | `Bool true -> valfun e2 rho kont | _ -> valfun e3 rho kont)
  | App (e1, e2)     ->      valfun e1 rho (function (`Fun f) -> valfun e2 rho (fun v -> f v kont))
  | Letrec (fname, (argname, e1, e2)) ->
    (* let rec rho' = update_rho fname (`Fun (fun v k -> valfun e1 (update_rho argname v rho') k)) rho *)
    let rec rho' = Env (fun x ->
      if x = fname then `Fun (fun v k -> valfun e1 (update_rho argname v rho') k) else access_rho x rho)
    in valfun e2 rho' kont
  | Let (valname, e1, e2) -> valfun e1 rho (fun res -> valfun e2 (update_rho valname res rho) kont)
  (* Mandatory otherwise ocaml says variant type does not allow... *)
  | AnnExpr _ -> failwith "No annotation allowed in the expression"
  (* "Primitive" expressions *)
  | _ -> g_lambda_primitive valfun e rho kont 

(* f rond g *)
let (>>) f g = fun x -> f (g x)
    
(* Note zoe: without functional : eval_AnnExpr (AnnExpr) rho kont =
   ...  For each function, eval_*, we have to extend it (Note: with an
   implementation in a first-order language we will not care -->
   generation of each function extension.)
   ('_a, 'm) t_lambda -> ('_a -> '_b, 'm) t_lambda 
   An example of Vi : V_Lam : S_Lam -> Env -> Kont -> 'a t_lambda_type
 *)
let over_g_lambda monitor_pre monitor_post (over_valfun:('x,'m) t_lambda) : ('x,'m) t_lambda =
  fun over_e rho kont -> match over_e with
    | AnnExpr (ann, over_e') ->
      let updPre  = monitor_pre ann over_e' rho in
      let updPost = monitor_post ann over_e' rho in
      let (k_post:'y kont) = (fun v ->
          (* I "overtyped" the types... *)
          let Ans ans = (kont v) in Ans (ans >> (updPost v))) in 
      let Ans ans' = (over_valfun over_e' rho k_post) in
      Ans (ans' >> updPre)
        
    | _ ->
      g_lambda over_valfun over_e rho kont
            
let empty_env = Env (fun i -> failwith ("Empty environment : "^i))

(* phi : A*i -> Ans *)
let k_init_param (finalProcessing: ('a denval -> 'b)) = fun v -> Ans (finalProcessing v)

