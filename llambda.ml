(** ----------------------------------------------------------------
 * Paper experiment: 
 *   Monitoring Semantics : A Formal framework for Specifying, Implementing,
 *   and Reasoning about Execution Monitors.
 * Standard continuation semantics
 *
 * ---------------------------------------------------------------- **)

open Fixpoint
(* ----------------------------------------------------------------
   Abstract Syntax
 ------------------------------------------------------------------ *)

type con = BOOL of bool | NAT of int
and id = string
and expr =
  | Con of con
  | Id of id
  | Lam of id * expr
  | Cond of expr * expr * expr
  | App of expr * expr
  | Letrec of id * (id * expr * expr)
(* "Primitive" expressions *)
  | Eq of expr * expr
  | Minus of expr * expr
  | Mult of expr * expr
      
let ast0_fact =
  Letrec ("fact",
          ("n",
               Cond (
                 Eq (Id "n", Con (NAT 1)),
                 Con (NAT 1),
                 Mult (Id "n",  App (Id "fact", Minus (Id "n", Con (NAT 1))))
               ),
           App (Id "fact", Con (NAT 4))))

(* ----------------------------------------------------------------
   Semantic Algebras
 ------------------------------------------------------------------ *)

(* Basic values Bas *)
type basv = [ `Int of int | `Bool of bool ]
(* Function values Fun *)
type  'a funv = 'a denval -> 'a kont -> 'a ans
(* Denotable values V *)
and  'a denval = [ basv | `Fun of 'a funv ]
(* Answers Ans. Not polymorphic to start.
   TODO: This is one of the places where the semantics will need to be extended.
 *)
and  'a ans = Ans of 'a
(* Environments Env *)
and  'a env = Env of (string -> 'a denval)
(* Expression continuations Kont *)
and  'a kont = 'a denval -> 'a ans


(* Store update *)
let update_rho i x = function Env rho ->
  Env (fun j -> if i = j then x else rho j)
let access_rho i = function Env rho -> rho i
(* Using wrapped type Ans:  
   let rec fac n (Ans k) = 
   if n = 0 then k 1 
   else fac (n-1) (Ans (fun r -> k (r*n)));; 
   fac 5 (Ans (fun x -> Printf.printf "result: %d" x));;
 *)

(* ----------------------------------------------------------------
   Valuation functional
 ------------------------------------------------------------------ *)

(* type t_i = syntax_i -> arg*_i -> kont_i -> ans with konti = arg*i -> ans *)
type 'a t_lambda_type =  expr -> 'a env -> 'a kont -> 'a ans

(*kfun : con -> denval *)
let kfun = function BOOL b -> `Bool b | NAT n -> `Int n
    
(* g_lambda : ValuationFunction -> 
   SyntaxExpression -> Environment -> Continuation -> 'a T_lambda
i.e.
   type 'a g_lambda = 'a t_lambda -> 'a t_lambda *)
let g_lambda valfun e rho kont = match e with
  | Con k -> kont (kfun k)
  | Id i  -> kont (access_rho i rho)
  | Lam (arg, ebody) -> kont (`Fun (fun v kont' -> valfun ebody (update_rho arg v rho) kont'))
  | Cond (e1, e2, e3) ->
    (valfun e1 rho (function
      (* Ocaml type : we must be exhaustive otherwise it does not compile *)
      | `Fun f -> failwith "Type error"
      | `Int n -> failwith "Type error"
      | `Bool b ->
        if b = true then valfun e2 rho kont else (Printf.printf "b false%!"; valfun e3 rho kont)))
  | App (e1, e2) -> valfun e1 rho (function (`Fun f) ->
      valfun e2 rho (fun v -> f v kont))
  | Letrec (fname, (argname, e1, e2)) ->
    (* let rec rho' = ... rho' ... is not allowed. E.g., above code yields
     error "not allowed as right-hand side of let rec" *)
    (* let rec rho' = update_rho fname (`Fun (fun v k -> valfun e1 (update_rho argname v rho') k)) rho *)
    let rec rho' = Env (fun x ->
      if x = fname
      then `Fun (fun v k -> valfun e1 (update_rho argname v rho') k)
      else access_rho x rho)
    
    in valfun e2 rho' kont
  (* "Primitive" expressions *)
  | Eq (e1, e2) -> valfun e1 rho ( fun (`Int v1) -> (valfun e2 rho (fun (`Int v2) -> kont (`Bool (
    Printf.printf "%d%!" (v1); v1 = v2)))))
  | Minus (e1, e2) -> valfun e1 rho (fun (`Int v1) -> (valfun e2 rho (fun (`Int v2) -> kont (`Int (v1 - v2)))))
  | Mult (e1, e2) -> valfun e1 rho (fun (`Int v1) -> (valfun e2 rho (fun (`Int v2) -> kont (`Int (v1 * v2)))))
  


    
let empty_env = Env (fun i -> failwith ("Empty environment : "^i))
(*
  Test in ocaml toplevel : 
  #load "fixpoint.cmo";;
  #use "llambda.ml";;
 *)
let string_of_denval = function
  | `Int  i -> string_of_int i
  | `Bool b -> string_of_bool b
  | `Fun f -> "Function...."

let k_init_param (finalProcessing: ('a denval -> 'b)) = fun x -> Ans (finalProcessing x)
(* phi : A*i -> Ans *)
let k_init1 phi = fun v -> (phi v)
(* Page 7 : std *)
let k_init_str = k_init_param (fun v -> "The result is "^(string_of_denval v))
  
let _ =
  Printf.printf "A factorial : " ;
  (FixNative.fix g_lambda) ast0_fact empty_env k_init_str
