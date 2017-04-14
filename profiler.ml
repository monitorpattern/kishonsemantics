(** 

Description: 
    This file is the first monitor implementation
    following the Kishak et al.'s monitoring framework in their ICFP
    paper. It counts the number of calls for the annotated
    functions/expressions concerned by this monitoring.  Annotations are
    "A" and "B".  A more tidy profiler is implemented in profiler2.ml

Note: 
    Comments related to the "unfriendly" naming of functions
*)
open LlambdaAnn
open Fixpoint
open Printf
(** ----------------------------------------------------------------
   Monitor Syntax
   ------------------------------------------------------------------ *)
type profiler_expr = string LlambdaAnn.ann
    
(** ---------------------------------------------------------------- 
    Example function : 
    - factorial applied to five.
    ---------------------------------------------------------------- *)
let ast0_fact_ann =
  Letrec ("fact",
          ("n",
           Cond (
             Eq (Id "n", Con (NAT 0)),
             AnnExpr (Ann "A", Con (NAT 1)),
             AnnExpr (Ann "B", Mult (Id "n",  App (Id "fact", Minus (Id "n", Con (NAT 1)))))
           ),
           App (Id "fact", Con (NAT 10))))

(* REF:    http://www.cs.utsa.edu/~wagner/CS3343/recursion/fibrecurs.html
    
n  F(n) calls
-------------
0   0       1
1   1       1
2   1       3
3   2       5
4   3       9
5   5      15
6   8      25
7   13     41
8   21     67
9   34    109

	

 n    F(n)          Elapsed time   Calls
------------------------------------------------
 5  5                  0.002 sec.  15
10  55                 0.005 sec.  177
15  610                0.007 sec.  1973
20  6765               0.007 sec.  21891
25  75025              0.012 sec.  242785
30  832040             0.061 sec.  2692537
35  9227465            0.516 sec.  29860703
40  102334155          5.006 sec.  331160281
45  1134903170        51.297 sec.  3672623805
50  12586269025      573.708 sec.  40730022147
55  139583862445    6436.252 sec.  451702867433
60  1548008755920  69839.095 sec.  5009461563921

 *)
    
let ast0_fibo_ann =
  Letrec ("fibo",
          ("n",
           AnnExpr(Ann "B", Cond (
             Leq (Id "n", Con (NAT 1)),
             AnnExpr (Ann "A", Id "n"),
             (* Plus operator : implicit Application *)
             Plus ( App (Id "fibo",  Minus (Id "n", Con (NAT 1)) ),
                    App (Id "fibo",  Minus (Id "n", Con (NAT 2)) ))
           )),
           App (Id "fibo", Con (NAT 21))))
(* fib 20 -> < 10946, 21890 > ; value : 6765
   fib 22 -> stack overflow with the annotations.
!! NOTE: The more we add annotations, the lower is the stack-overflow threshhold
 *)
    
(** ----------------------------------------------------------------
   Monitor Algebras 
   ------------------------------------------------------------------ *)

type mms = MS of (int * int)

let inc_A (MS (n1, n2)) = MS (n1 + 1, n2)
let inc_B (MS (n1, n2)) = MS (n1, n2 + 1)
let init_state = MS (0, 0)

let string_of_ms (MS (x, y)) = Printf.sprintf "< %d, %d >" x y

(** ----------------------------------------------------------------
   Monitoring Functions 
    (set of pairs of mon.fun. one pair for each valfun of Den)
   ------------------------------------------------------------------ *)
  
(* let monitor_pre (ann:ann) (o_e:expr) (rho:'a env) = fun mms -> failwith "Not implemented"
 * let monitor_post (ann:ann) (o_e:expr)(rho:'a env) (v:denval) = fun mms -> failwith "Not implemented" *)

let monitor_pre (ann:'m ann) (e:'m expr) (rho:'a env) (sigma:mms) =
  match ann with
  | Ann "A" -> inc_A sigma
  | Ann "B" -> inc_B sigma

let monitor_post ann e rho v sigma = sigma

(* phi : function of answer algebra, mapping the result to a printing of strings *)
let phi = fun v -> Printf.printf "[Phi] result is: %s\n" (string_of_denval v)

(* Get the greek letters from the paper to follow easily the experiment *)
(*  theta alpha = lambda sigma -> (alpha, sigma) *)
(*  'a denval -> (mms -> unit LlambdaAnn.ans * mms) LlambdaAnn.ans *)
let over_phi = fun x ->
  (* theta_? : answer transformer -- transforms an answer into a pair
     answer and monitor state. *)
  let theta_profiler ans = Ans (fun (ms:mms) -> ans, ms) in
  theta_profiler (Ans (phi x))


(** ----------------------------------------------------------------
    Unit Tests
   ------------------------------------------------------------------ *)
    
let test_ast ast =
  Printf.printf "[Tested function] %s\n%!" (LlambdaAnn.string_of_expr ast);
  (FixNative.fix (over_g_lambda monitor_pre monitor_post))
  (* fun v -> over_phi v -> initial continuation with MS *)
  ast empty_env (fun v -> over_phi v)

(** ----------------------------------------------------------------
    Main
  ------------------------------------------------------------------ *)

let test () =
  Printf.printf "\n----------------------------- \nTesting the Profiler:\n%!";
  Printf.printf "----------------------------- \n%!";
  let Ans afunc = test_ast ast0_fact_ann in
  let _ans, final_mms = afunc init_state in
  Printf.printf "[Profiling] Final MState (numbers of calls) = %s\n\n" (string_of_ms final_mms)
  ;
  let Ans fibofunc = test_ast ast0_fibo_ann in
  let _ans, final_mms = fibofunc init_state in
  Printf.printf "[Profiling] Fibo Final MState (numbers of calls) = %s\n" (string_of_ms final_mms)
  

let _ =
  if (Array.length Sys.argv > 1) && (Sys.argv.(1) = "all" || Sys.argv.(1) = "profiler") then
    test ()














                                 
