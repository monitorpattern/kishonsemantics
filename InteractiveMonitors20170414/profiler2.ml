open LlambdaAst
open LlambdaAlg
open LlambdaInt
open Fixpoint
open Printf
(** ----------------------------------------------------------------
   Monitor Syntax
   ------------------------------------------------------------------ *)
type profiler_expr = string LlambdaAst.ann (* string as function name. *)

(** ----------------------------------------------------------------
   Monitor Algebras 
   ------------------------------------------------------------------ *)
type cenv = string -> int
type mms = MS of cenv

let init_cenv = fun i -> 0
let update_cenv i v rho_c = fun j -> if i = j then v else rho_c j
let access_cenv i rho_c = rho_c i
(* FIXME : change cenv in a list instead of function *)
let dom_cenv = ["fact"; "mult"; "fibo"]

(* return a cenv with f value updated *)
let incCtr f (MS rho_c) = MS (let n = (access_cenv f rho_c) + 1 in update_cenv f n rho_c)
let init_state = MS (init_cenv)

let string_of_ms (MS rho_c) =
  (String.concat "; " (List.map (fun x -> x ^ " -> "^ (string_of_int (access_cenv x rho_c))) dom_cenv))^"\n"

(* --- start-of-attempt --- *)
(* Set of functions picked from tracer for an 
Attempt of manipulating stdout as out_channel in pure functional prgming.... (what it is) *)
and addStream str o = output_string o str ; o (* modify o with side-effect *)
and initStream = stdout

(* -- end-of-attempt --- *)
(** ----------------------------------------------------------------
   Monitoring Functions 
    (set of pairs of mon.fun. one pair for each valfun of Den)
   ------------------------------------------------------------------ *)
  
(* let monitor_pre (ann:'m ann) (ast_e:'m expr) (rho:'a env) 
   = fun mms -> failwith "Not implemented"
   let monitor_post (ann:'m ann) (ast_e:'m expr)(rho:'a env) (v:'a denval) 
   = fun mms -> failwith "Not implemented" *)  
let monitor_pre (ann:'m ann) (e:'m expr) (rho:'a env) (sigma:mms) =
  let Ann f = ann in
  incCtr f sigma
let monitor_post ann e rho v sigma = sigma

(* phi : function of answer algebra, mapping the result to a printing of strings 
Difference with other profiler2 versions : returns a string. 
Map with kishon's jfp : phi is toAns
*)
let phi = (fun v -> addStream (Printf.sprintf "[Phi] result is: %s\n" (string_of_denval v)) stdout)

(* Get the greek letters from the paper to follow easily the experiment *)
(*  theta alpha = lambda sigma -> (alpha, sigma) *)
(*  'a denval -> (mms -> unit LlambdaAnn.ans * mms) LlambdaAnn.ans 
I guess this corresponds to IOMonitorType
*)
let over_phi = fun x ->
  (* theta_? : answer transformer -- transforms an answer into a pair
     answer and monitor state. *)
  let theta_profiler ans = (fun (ms:mms) (inChan:in_channel) -> inChan, ans, ms) in
  Ans (theta_profiler (Ans (phi x)))
    
(** ----------------------------------------------------------------
    Unit Tests
   ------------------------------------------------------------------ *)   
(*  val test_profiler ast: 'a -> (mms -> unit LlambdaAnn.ans * mms) LlambdaAnn.ans = over_ans *)
let test_profiler ast = (FixNative.fix (over_g_lambda monitor_pre monitor_post))
  (* fun v -> over_phi v -> initial continuation with MS *)
  ast empty_env (fun v -> over_phi v)

let test () =
  Printf.printf "\n----------------------------- \n(Interactive) Testing the Profiler (Figure 6):\n%!";
  Printf.printf "----------------------------- \n%!";
  (* List.iter (fun (optname, ast) ->  *)
  let optname = "fact" and ast = LlambdaAst.ast_ann_fact_five_mult in
  let Ans afunc = test_profiler ast in
  let inchan, _ans, final_mms = afunc init_state stdin in
  Printf.printf "[Profiling] %s Final MState (numbers of calls) = %s\n"
    optname (string_of_ms final_mms)
  (* ) LlambdaAstExamples.global_ast_map *)

(** ----------------------------------------------------------------
    Main
  ------------------------------------------------------------------ *)
    
let _ =
    test ()







                                 
