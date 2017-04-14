(** 

Description: 
    A demon applied to a function that manipulates lists. 
    The calculated lists that are not sorted (the demon event "is_sorted") 
    during the manipulation are detected.
Note:
    For the naming of functions in this file, see comments in profiler.ml
*)
open LlambdaAnn
open Fixpoint
open Printf
(** ----------------------------------------------------------------
   Monitor Syntax
   ------------------------------------------------------------------ *)
type demon_expr = string LlambdaAnn.ann (* string as the name of element to catch. *)
(** ---------------------------------------------------------------- 
    Example function : 
    inclist p.21
    ---------------------------------------------------------------- *)
let ast0_inclist_Letrec3 =
  Let ("l3",
       AnnExpr (Ann "l3", App (App (Id "inclist", Id "l2"), Con (LIST []))),
       Id "l3"
  )

let ast0_inclist_Letrec2 = 
    Let ("l2",
         AnnExpr (Ann "l2", App (App (Id "inclist", Id "l1"), Con (LIST []))),
         ast0_inclist_Letrec3
    )

let ast0_inclist_Letrec1 =
  Let ("l1",
       AnnExpr (Ann "l1", App (App (Id "inclist", Con (LIST [1; 10; 100])), Con (LIST []))),
       ast0_inclist_Letrec2
  )
    
let ast0_inclist =
  Letrec ("inclist",
          ("l0",
           Lam ("acc",
                Cond (Eq (Id "l0", Con (LIST [])),
                      Id "acc",
                      App (App (Id "inclist", Tail "l0"),
                           Cons (Plus (Head "l0", Con (NAT 1)), "acc")
                      )
                )),
           ast0_inclist_Letrec1
           ))

(* let rec collatzVol un = if un==1 then 1 else if un mod 2 = 0 then collatzVol(un/2) else collatzVol (3*un+1);; *)
(* let rec collatz a n = if n = 0 then a else if a mod 2 = 0 then collatz (a/2) (n-1) else collatz (3*a+1) (n-1);;  *)
let ast0_collatzVol =
  Letrec ("collatzVol",
          ("u",
           Cond(Eq(Id "u", Con(NAT 1)),
                Con(NAT 1),
                Cond(Eq(Mod (Id "u", Con(NAT 2)), Con(NAT 0)),
                     AnnExpr(Ann "coll1", App (Id "collatzVol", Div(Id "u", Con (NAT 2)))),
                     AnnExpr(Ann "coll2", App (Id "collatzVol", Succ(Mult(Id "u", Con (NAT 3) ))))))
             ,
           App (Id "collatzVol", Con(NAT 15)))) 
            
(** ----------------------------------------------------------------
   Monitor Algebras 
    ------------------------------------------------------------------ *)
type mms = MS of string list
(* I. State *)    
let rec init_state : mms = MS []

let string_of_ms (MS l) = String.concat ";" l
  
(** ----------------------------------------------------------------
   Monitoring Functions 
    (set of pairs of mon.fun. one pair for each valfun of Den)
   ------------------------------------------------------------------ *)
  
(* let monitor_pre (ann:'m ann) (o_e:'m expr) (rho:'a env) = fun mms -> failwith "Not implemented"
 * let monitor_post (ann:ann) (o_e:expr)(rho:'a env) (v:'a denval) = fun mms -> failwith "Not implemented" *)
(* val monitor_pre *)
let monitor_pre (ann:'m ann) (e:'m expr) (rho:'a env) (sigma:mms) : mms=
  sigma
    
let monitor_post ann e rho (v:'a denval) sigma : mms =
  let Ann lName = ann in
  let MS l = sigma in
  let rec is_sorted = function
    | [] -> true
    | x::xs -> (match xs with
        | [] -> true
        | y::ys -> (x <= y && is_sorted xs))
  in
  match v with
    | `List vl ->
      if is_sorted vl then sigma else MS (lName::l)
    | _ -> failwith "Wrong type"

let monitor_pre0 ann e rho sigma =
  Printf.printf " %s " (string_of_denval (access_rho "u" rho)); sigma
let monitor_post0 ann e rho v sigma : mms = 
   let Ann lName = ann in
   let MS l = sigma in
   let rec is_odd = function
     | `Int x -> x mod 2 = 1 
     | _ -> false   in
   (* hacky test of demon on collatz *)
   let u = (access_rho "u" rho) in
   if not (is_odd u) then sigma else MS ((string_of_denval u) :: l)

(* phi : function of answer algebra, mapping the result to a printing of strings *)
let phi = (fun v -> Printf.printf "[Phi] result is: %s\n" (string_of_denval v))

(* Get the greek letters from the paper to follow easily the experiment *)
(*  theta alpha = lambda sigma -> (alpha, sigma) *)
let over_phi = fun x ->
  (* theta_? : answer transformer -- transforms an answer into a pair
     answer and monitor state. *)
  let theta ans = Ans (fun (ms:mms) -> ans, ms) in
  theta (Ans (phi x))


(** ----------------------------------------------------------------
    Unit Tests
   ------------------------------------------------------------------ *)
    
let test_ast ast (monitor_pre, monitor_post) =
  Printf.printf "[Tested function] %s\n%!" (LlambdaAnn.string_of_expr ast);
  (FixNative.fix (over_g_lambda monitor_pre monitor_post))
  ast empty_env (fun v -> over_phi v)
  
(** ----------------------------------------------------------------
    Main
  ------------------------------------------------------------------ *)
  
let test () =
  Printf.printf "\n----------------------------- \nTesting the Demon (Version 1) :\n%!";
  Printf.printf "----------------------------- \n%!";
  (* ------ Test with inclist ---------------- *)
  let Ans afunc = test_ast ast0_inclist (monitor_pre, monitor_post) in
  let _ans, ms = afunc init_state in
  Printf.printf "[Demon] Final MState %s \n\n" (string_of_ms ms);
  (* ------ Test with collatz flight function ---------------- *)  
  let Ans afunc = test_ast ast0_collatzVol (monitor_pre0, monitor_post0) in
  let _ans, ms = afunc init_state in
  Printf.printf "[Demon] Final MState %s \n\n" (string_of_ms ms)


let _ =
  if (Array.length Sys.argv > 1) && (Sys.argv.(1) = "all" || Sys.argv.(1) = "demon") then
    test ()













                                 
