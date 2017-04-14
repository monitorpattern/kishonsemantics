(** 

Description: 
    A typical profiler. The body of letrec expressions
    is annotated w.r.t the letrec function name.
Note:
    For the naming of functions in this file, see comments in profiler.ml
*)
open LlambdaAnn
open Fixpoint
open Printf
(** ----------------------------------------------------------------
   Monitor Syntax
   ------------------------------------------------------------------ *)
type profiler_expr = string LlambdaAnn.ann (* string as function name. *)   
(** ---------------------------------------------------------------- 
    Example function : 
    - factorial applied to five.
    ---------------------------------------------------------------- *)
let ast0_fact =
  Letrec ("fact",
          ("n",
           AnnExpr (Ann "fact",Cond (
             Eq (Id "n", Con (NAT 0)),
             Con (NAT 1),
             Mult (Id "n", App (Id "fact", Minus (Id "n", Con (NAT 1)))))),
           App (Id "fact", Con (NAT 3))))
    
let ast0_fact_ann =
  Letrec ("fact",
          ("n",
           AnnExpr (Ann "fact", Cond (
             Eq (Id "n", Con (NAT 0)),
             Con (NAT 1),
             App (App (Id "mult", Id "n"),  App (Id "fact", Minus (Id "n", Con (NAT 1)))))),
           App (Id "fact", Con (NAT 3))))

let ast0_fact_mult_ann =
  Letrec ("mult",
          ("x",
           Lam ("y",  AnnExpr (Ann "mult" , Mult (Id "x", Id "y"))),
           ast0_fact_ann))
(* The more we add annotations, the lower is the threshold over which a stack overflow occurs 
  Test with the naive 3 annotations on App fibo instead of the one wrapping the Cond. *)
let ast0_fibo_ann =
  Letrec ("fibo",
          ("n",
           AnnExpr (Ann "fibo", Cond (
             Leq (Id "n", Con (NAT 1)),
             Id "n",
             (* Plus operator : implicit Application *)
             Plus (  App (Id "fibo",  Minus (Id "n", Con (NAT 1)) ),
                     App (Id "fibo",  Minus (Id "n", Con (NAT 2)) ))
           )),
           App (Id "fibo", Con (NAT 21))))
(* fib 20 -> < 10946, 21890 > ; value : 6765
   fib 22 -> stack overflow *)
    
(** ----------------------------------------------------------------
   Monitor Algebras 
   ------------------------------------------------------------------ *)
type cenv = (string * int) list
type mms = MS of cenv

let init_cenv = []
let update_cenv i v rho_c = (i,v)::(List.remove_assoc i rho_c)
let access_cenv i rho_c = if List.mem_assoc i rho_c then List.assoc i rho_c else 0    
let incCtr f (MS rho_c) = MS (let n = (access_cenv f rho_c) + 1 in update_cenv f n rho_c)
let init_state = MS (init_cenv)
let string_of_ms (MS rho_c) =
  let dom_cenv = fst (List.split rho_c) in 
  (String.concat "; " (List.map (fun x -> x ^ " -> "^ (string_of_int (access_cenv x rho_c))) dom_cenv))^"\n"
  
(** ----------------------------------------------------------------
   Monitoring Functions 
    (set of pairs of mon.fun. one pair for each valfun of Den)
   ------------------------------------------------------------------ *)
  
let monitor_pre ann e rho sigma = let Ann f = ann in incCtr f sigma
let monitor_post ann e rho v sigma = sigma

let phi = fun v -> Printf.printf "[Phi] result is: %s\n" (string_of_denval v)

let over_phi = fun x ->
  let theta_profiler ans = (fun (ms:mms) -> ans, ms) in
  Ans (theta_profiler (Ans (phi x)))

(** ----------------------------------------------------------------
    Unit Tests
   ------------------------------------------------------------------ *)

let test_ast ast =
  Printf.printf "[Tested function] %s\n%!" (LlambdaAnn.string_of_expr ast);
  (FixNative.fix (over_g_lambda monitor_pre monitor_post))
  (* fun v -> over_phi v -> initial continuation with MS *)
  ast empty_env (fun v -> over_phi v)

(* [Doc comment] The type of answer.
val test0_fact : 'a -> (mms -> unit LlambdaAnn.ans * mms) LlambdaAnn.ans 
let test0_fact _thunk = (FixNative.fix g_lambda) ast0_fact empty_env (fun v -> over_phi v) *)

(** ----------------------------------------------------------------
    Main
  ------------------------------------------------------------------ *)

let test () =
  Printf.printf "\n----------------------------- \nTesting the Profiler (Figure 6):\n%!";
  Printf.printf "----------------------------- \n%!";
  let Ans afunc = test_ast ast0_fact_mult_ann in
  let _ans, final_mms = afunc init_state in
  Printf.printf "[Profiling] Final MState (numbers of calls) = %s\n" (string_of_ms final_mms)
  ;
  let Ans fibofunc = test_ast ast0_fibo_ann in
  let _ans, final_mms = fibofunc init_state in
  Printf.printf "[Profiling] Fibo Final MState (numbers of calls) = %s\n" (string_of_ms final_mms)  
  ;
  let Ans afunc = test_ast ast0_fact in
  let _ans, final_mms = afunc init_state in
  Printf.printf "[Profiling] Fibo Final MState (numbers of calls) = %s\n" (string_of_ms final_mms)

let _ =
  if (Array.length Sys.argv > 1) && (Sys.argv.(1) = "all" || Sys.argv.(1) = "profiler2") then
    test ()








                                 
