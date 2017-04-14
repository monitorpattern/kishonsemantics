(** ----------------------------------------------------------------
 * Paper experiment: 
 *   Monitoring Semantics : A Formal framework for Specifying, Implementing,
 *   and Reasoning about Execution Monitors.
 * + Semantics Directed Program Execution Monitoring - Authors: Kishon & Hudak
 * Standard continuation semantics (Fig. 2) And
 * Parameterized monitoring semantics (Fig. 3) *
 * FIXME : local variables are no more shown when show is asked in debugger
 * ---------------------------------------------------------------- **)
open Fixpoint

(* Abstract Syntax *)
open LlambdaAst
(* Semantic Algebras *)
open LlambdaAlg

(** ----------------------------------------------------------------
   Valuation functional
   ------------------------------------------------------------------ *)  
(* type t_i = syntax_i -> arg*_i -> kont_i -> ans 
   with konti = arg*i -> ans *)
type ('a,'m) t_lambda =  'm expr -> 'a env -> 'a kont -> 'a ans
(* val kfun : con -> denval *)
let kfun = function BOOL b -> `Bool b | NAT n -> `Int n | LIST l -> `List l
(* Return the primitive operator (+,-,* ) of the given expression (to ease tests...) *)
let bool_of_expr = function Leq _ -> (<=) | Eq _ -> (=) | _ -> failwith "Invalid boolean-operator"
(* Return the primitive operator (+,-,* ) of the given expression *)
let prim_of_expr = function Minus _ -> (-) | Plus _ -> (+) | Mult _ -> ( * ) | Div _ -> (/) | Mod _ -> ( mod ) | _ -> failwith "Invalid primitive-operator"
    
(* chunk of the valuation functional that handles primitive operations *)
let g_lambda_primitive (valfun:('a,'m) t_lambda) e rho kont =
  match e with 
    | Eq (e1, e2) | Leq (e1, e2) -> valfun e1 rho (fun v1 -> valfun e2 rho (fun v2 -> kont (`Bool ((bool_of_expr e) v1 v2))))
    | Minus (e1, e2) | Plus (e1, e2) | Mult (e1, e2) | Div (e1, e2) | Mod (e1, e2) ->
      valfun e1 rho (function
        |(`Int v1) -> valfun e2 rho (fun (`Int v2) -> kont (`Int ((prim_of_expr e) v1 v2)))
        | x -> failwith ("Pattern fail, type : "^(string_of_denval x)^" -  the e : "^(string_of_expr e)))
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

(* f <=> g - cf. JFP 
   Replaces (>>) in interactive monitoring 

  ('a -> 'b -> 'c * outChannel) ->
  ('d -> inChannel -> 'b * outChannel * 'a) -> 'd -> inChannel -> 'b * string =

*)
let (<=>) evalActivity monitorActivity = fun monState input -> 
  let (input', output', monState') = monitorActivity monState input in
  let (input'', output'') = evalActivity monState' input' in
  (* FIXME-HACK If there is nothing to display, ignore. 
   <=> is called a lot of times.... 4*number of calls *)
  if not (IO.isEmpty output'') then 
    Printf.printf "Output? %s.\n%!" (output'');
  (* (input', (IO.concat output' output'')) *)
  (input', "")

(* output' ++ output'' -> in Haskell -- make pipe in ocaml for stdin/stdout  *) 

(* JFP :
   monitor_pre = preFun 
   monitor_post = postFun
   preMonitor = updPre
   postMonitor = updPost
   over_valfun = the newEval argument
*)
let over_g_lambda monitor_pre monitor_post (over_valfun:('x,'m) t_lambda) : ('x,'m) t_lambda =
  (* \ exp semArg k *)
  fun over_e rho kont -> match over_e with      
    | AnnExpr (ann, over_e') ->
      let updPre  = monitor_pre ann over_e' rho in
      let updPost = monitor_post ann over_e' rho in
      let k_post = fun v ->
        let Ans ans = kont v in Ans (ans <=> (updPost v)) in 
      let Ans ans' = over_valfun over_e' rho k_post in
      Ans (ans' <=> updPre)
    (* | Con _ | Id _ | Unit ->
     *   Printf.printf "g_lambda...%s\n%!" (string_of_expr over_e);
     *   g_lambda over_valfun over_e rho kont *)
    | _ ->
      let updPre  = monitor_pre LBreak over_e rho in
      let updPost = monitor_post LBreak over_e rho in
      let k_post = fun v ->
        let Ans ans = (kont v) in Ans (ans <=> (updPost v)) in
      (* Infinite loop in next line *)
      let Ans ans' =   g_lambda over_valfun over_e rho k_post in
      Ans (ans' <=> updPre)
    (* in Standard Execution, still working *)
            
let empty_env = Env (fun i -> failwith ("Empty environment : "^i))

(* phi : A*i -> Ans *)
let k_init_param (finalProcessing: ('a denval -> 'b)) = fun v -> Ans (finalProcessing v)

(** Making the combined monitor/interpreter interactive 
    Paper: Semantics Directed Program Execution Monitoring - Authors: Kishon & Hudak
*)  
type dialogue = string list -> string list

