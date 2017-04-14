(**
Description:
   A typical collecting monitor ("a la collecting interpreter" - see ICFP...).
Note:
    For the naming of functions in this file, see comments in profiler.ml
*)
open LlambdaAnn
open Fixpoint
open Printf
(* Global variable *)
let the_filename = "ztrace.txt"

(** ----------------------------------------------------------------
    Monitor Syntax
    ------------------------------------------------------------------ *)
type tracer_expr = string LlambdaAnn.ann (* string as function name. *)

(** ---------------------------------------------------------------- 
    Example functions
    ---------------------------------------------------------------- *)
let ast0_collatzVol =
  Letrec ("collatzVol",
          ("u",
           Cond(AnnExpr( Ann "test", Eq(Id "u", Con(NAT 1))),
                Con(NAT 1),
                AnnExpr(Ann "u", Cond(Eq(Mod (Id "u", Con(NAT 2)), Con(NAT 0)),
                                                      App (Id "collatzVol", Div(Id "u", Con (NAT 2))),
                                                      App (Id "collatzVol", Succ(Mult(Id "u", Con (NAT 3) ))))))
             ,
           App (Id "collatzVol", Con(NAT 15))))

let ast0_fact =
  Letrec ("fact",
          (  "n",
             Cond (
               AnnExpr(Ann "test", Eq (Id "n", Con (NAT 0))),
               Con (NAT 1),
               Mult (AnnExpr(Ann "n", Id "n"),  App (Id "fact", Minus (Id "n", Con (NAT 1))))
               ),
             App (Id "fact", Con (NAT 10))))

let ast0_collatz =
  Letrec ("collatz",
          ("u0",
           Lam ("n",
           AnnExpr(Ann "cond",Cond(AnnExpr(Ann "test", Eq(Id "n", Con(NAT 1))),
                Id "u0",
                Cond(Eq(Mod (AnnExpr(Ann "u0", Id "u0"), Con(NAT 2)), Con(NAT 0)),
                                                      App (App (Id "collatz", Div(Id "u0", Con (NAT 2))), Minus (Id "n", Con (NAT 1)) ),
                     App (App (Id "collatz", Succ(Mult(Id "u0", Con (NAT 3)))), Minus (Id "n", Con (NAT 1)) ) ))
           )
           )
             ,
           App (App (Id "collatz", Con(NAT 15)), Con(NAT 40))))
    
(** ----------------------------------------------------------------
    Monitor Algebras 
    ------------------------------------------------------------------ *)
(* Number of calls, values of second arg in Ann before monitoring, values of second arg in Ann after monitoring *)
type mms = MS of (string list * (string -> basv list)) (* avoir denval because polymorphic 'a'a'a'a*)
(* I. State *)    
let init_state : mms = MS ([], fun i -> [])

let access_collRho varName collRho = collRho (varName)
let update_collRho varName varValue (MS (varList, collRho)) =
  let varList' = if not (List.exists ( (=) varName ) varList) then varName::varList else varList in
  let varVals  = access_collRho varName collRho in
  let collRho' = fun i -> if i = varName && not (List.exists ((=) varValue) varVals) then 
      varValue::varVals else access_collRho i collRho in
  MS (varList', collRho') 
  
let string_of_ms (MS (varl, collRho)) = "Monitor State:"
  ^  "\n  Variables: [" ^ (String.concat "; " varl) ^ "]"
  ^  "\n  Environment:  [" ^
    (String.concat "; "
       (List.map
          (fun var -> var
            ^ " |-> {"
            ^ (String.concat ","
                 (List.map (fun x -> string_of_basv x) (access_collRho var collRho)))
            ^ "}"
          ) varl)) ^ "]"

(** ----------------------------------------------------------------
    Monitoring Functions 
    (set of pairs of mon.fun. one pair for each valfun of Den)
    ------------------------------------------------------------------ *)

let monitor_pre  (ann:'m ann) (e:'m expr) (rho:'a env) (sigma:mms) : mms = sigma
let monitor_post (ann:'m ann) (e:'m expr) (rho:'a env) (v:'a denval) (sigma:mms) : mms =
  let Ann varName = ann in update_collRho varName (basv_of_denval v) sigma
    
let phi = (fun v -> Printf.printf "[Phi] result is: %s\n" (string_of_denval v))

let over_phi = fun x ->
  let theta ans = Ans (fun (ms:mms) -> ans, ms) in
  theta (Ans (phi x))


(** ----------------------------------------------------------------
    Unit Tests
    ------------------------------------------------------------------ *)
    
let test0_ast ast =
  Printf.printf "[Tested function] %s\n%!" (LlambdaAnn.string_of_expr ast);
  (FixNative.fix (over_g_lambda monitor_pre monitor_post))
  ast empty_env (fun v -> over_phi v)
  
(** ----------------------------------------------------------------
    Main
    ------------------------------------------------------------------ *)
  
let test () =
  Printf.printf "\n----------------------------- \nTesting the Collecting Monitor :\n%!";
  Printf.printf "----------------------------- \n%!";
  (* ------ Test with collatzVol ---------------- *)
  let Ans afunc = test0_ast ast0_collatzVol in
  let _ans, ms = afunc init_state in
  Printf.printf "[Demon] Final MState %s \n\n" (string_of_ms ms)
  ;
  let Ans afunc = test0_ast ast0_fact in
  let _ans, ms = afunc init_state in
  Printf.printf "[Demon] Final MState %s \n\n" (string_of_ms ms)
  ;
  Printf.printf "Collatz : %s\n%!" (string_of_expr ast0_collatz);
  let Ans afunc = test0_ast ast0_collatz in
  let _ans, ms = afunc init_state in
  Printf.printf "[Demon] Final MState %s \n\n" (string_of_ms ms)


let _ =
  if (Array.length Sys.argv > 1) && (Sys.argv.(1) = "all" || Sys.argv.(1) = "collector") then
    test ()














    
