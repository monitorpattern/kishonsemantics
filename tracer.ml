(** 

Description: 
    A typical tracer.
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
type functionHeader = string * string list (* fname * list of arguments *)
type tracer_expr = functionHeader LlambdaAnn.ann (* string as function name. *)
(** ---------------------------------------------------------------- 
    Example function : 
    - factorial applied to five.
    ---------------------------------------------------------------- *)
let ast0_fact_ann =
  Letrec ("fact",
          ("n",
           AnnExpr (Ann ("fact", ["n"]), Cond (
             Eq (Id "n", Con (NAT 0)),
             Con (NAT 1),
             App (App (Id "mult", Id "n"),  App (Id "fact", Minus (Id "n", Con (NAT 1)))))),
           App (Id "fact", Con (NAT 5))))

let ast0_fact_ann2 =
  Letrec ("fact",
          ("n",
           Lam ("acc",
                (* NOTE : arguments in Ann must be in the scope of their declaration *)
                AnnExpr (Ann ("fact", ["n";"acc"]), Cond (
                  Eq (Id "n", Con (NAT 0)),
                  Id "acc",
                  App (App (Id "fact",                                 
                            Minus (Id "n", Con (NAT 1))),
                       App (App (Id "mult", Id "n"),
                            Id "acc"))  
                ))),
          App (App (Id "fact", Con (NAT 5)), Con (NAT 1) )))
             
    
let ast0_fact_mult_ann =
  Letrec ("mult",
          ("x",
           Lam ("y",  AnnExpr (Ann ("mult", ["x"; "y"]) , Mult (Id "x", Id "y"))),
           ast0_fact_ann))

let ast0_fact_mult_ann2 =
  Letrec ("mult",
          ("x",
           Lam ("y",  AnnExpr (Ann ("mult", ["x"; "y"]) , Mult (Id "x", Id "y"))),
           ast0_fact_ann2))

    
(* The more we add annotations, the lower is the threshold over which a stack overflow occurs 
  Test with the naive 3 annotations on App fibo instead of the one wrapping the Cond. *)
let ast0_fibo_ann =
  Letrec ("fibo",
          ("n",
           AnnExpr (Ann ("fibo", ["n"]), Cond (
             Leq (Id "n", Con (NAT 1)),
             Id "n",
             (* Plus operator : implicit Application *)
             Plus (  App (Id "fibo",  Minus (Id "n", Con (NAT 1)) ),
                     App (Id "fibo",  Minus (Id "n", Con (NAT 2)) ))
           )),
           App (Id "fibo", Con (NAT 21))))
(* fib 20 -> < 10946, 21890 > ; value : 6765
   fib 22 -> stack overflow
 *)

let ast0_collatzVol =
  Letrec ("collatzVol",
          ("u",
           AnnExpr(Ann ("collatzVol", ["u"]), Cond(Eq(Id "u", Con(NAT 1)),
                Con(NAT 1),
                Cond(Eq(Mod (Id "u", Con(NAT 2)), Con(NAT 0)),
                                                      App (Id "collatzVol", Div(Id "u", Con (NAT 2))),
                                                      App (Id "collatzVol", Succ(Mult(Id "u", Con (NAT 3) ))))))
             ,
           App (Id "collatzVol", Con(NAT 15))))
    
let ast0_collatz =
  Letrec ("collatz",
          ("u0",
           Lam ("n",
           AnnExpr(Ann ("collatz", ["u0"; "n"]),Cond(Eq(Id "n", Con(NAT 1)),
                Id "u0",
                Cond(Eq(Mod (Id "u0", Con(NAT 2)), Con(NAT 0)),
                                                      App (App (Id "collatz", Div(Id "u0", Con (NAT 2))), Minus (Id "n", Con (NAT 1)) ),
                     App (App (Id "collatz", Succ(Mult(Id "u0", Con (NAT 3)))), Minus (Id "n", Con (NAT 1)) ) ))
           )
           )
             ,
           App (App (Id "collatz", Con(NAT 15)), Con(NAT 42))))

let ast0_hanoi =
  Letrec ("hanoi",
          ("n",
           Lam ("D",
                Lam("A",
                    Lam ("I",
                         AnnExpr(Ann ("hanoi", ["n"; "D"; "A"; "I"]),
                         Cond(Leq(Con(NAT 1), Id "n"),
                              Let ("0",
                                           App(App(App(App(Id "hanoi", Minus(Id "n", Con(NAT 1))), Id "D"), Id "I"), Id "A"),
                                           App(App(App(App(Id "hanoi", Minus(Id "n", Con(NAT 1))), Id "I"), Id "A"), Id "D")
                              ), Unit
                         )) (* idle operation for else *)
                    ))),
                App(App(App(App(Id "hanoi", Con(NAT 5)), Con(NAT 1)), Con(NAT 3)), Con(NAT 2))))
(** ----------------------------------------------------------------
   Monitor Algebras 
    ------------------------------------------------------------------ *)
type mms = MS of out_channel * int
(* I. State *)    
let rec init_state : mms = MS (initStream, 0)
(* II. Output channel and streams... *)    
and printChan x n o = (indent n o); addStream x o
and indent n o = (addStream " " o); spaces n o
and spaces num o = match num with
  | 0 -> ()
  | n ->  (addStream "|\t" o); spaces (n-1) o
(* III Stream *)
and addStream x o = output_string o x
and initStream = stdout
  (* open_out_gen [Open_creat;Open_trunc; Open_append] 0o666 the_filename *)

let string_of_ms (MS (s, c)) = failwith "hu"
  
(** ----------------------------------------------------------------
   Monitoring Functions 
    (set of pairs of mon.fun. one pair for each valfun of Den)
   ------------------------------------------------------------------ *)
  
let monitor_pre (ann:'m ann) (e:'m expr) (rho:'a env) (sigma:mms) : mms=
  let Ann (fName, argList) = ann in
  let MS (o, n) = sigma in
  let argStr = String.concat ", " (List.map (fun xi -> string_of_denval (access_rho xi rho)) argList) in
  let trace =  "[" ^ (String.uppercase fName) ^ " receives ("  ^  argStr ^ ")]\n" in
  printChan trace n o;
  MS (o, n+1)
    
let monitor_post ann e rho (v:'a denval) sigma : mms =
  let Ann (fName, _) = ann in
  let MS (o, n) = sigma in
  let trace = "[" ^ (String.uppercase fName) ^ " returns " ^ (string_of_denval v) ^ " ]\n" in
  printChan trace (n-1) o;
  MS (o, n-1)

let phi = (fun v -> Printf.printf "[Phi] result is: %s\n" (string_of_denval v))

let over_phi = fun x ->
  let theta ans = (fun (ms:mms) -> ans, ms) in
  Ans (theta (Ans (phi x)))

(** ----------------------------------------------------------------
    Unit Tests
   ------------------------------------------------------------------ *)
let test_tracer_on_ast ast =
  Printf.printf "[Tested function] %s\n%!" (LlambdaAnn.string_of_expr ast);
  (FixNative.fix (over_g_lambda monitor_pre monitor_post))
  ast empty_env (fun v -> over_phi v)

let global_ast_map =
  [ ("fact", ast0_fact_mult_ann);
    ("fact2", ast0_fact_mult_ann2);
    ("fibo", ast0_fibo_ann);
    ("collatzVol", ast0_collatzVol);
    ("collatz", ast0_collatz);
    ("hanoi", ast0_hanoi); ]
(** ----------------------------------------------------------------
    Main
  ------------------------------------------------------------------ *)
(* Helper function *)
let print_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = String.create n in
  really_input ic s 0 n;
  close_in ic;
  Printf.printf "%s%!" s

(* FIXME: Close the stream when reaching the last call of monitor_post. 
   with close_out o; *)

(**  option : a string in the list global_ast_map *)
let test option =
  Printf.printf "\n----------------------------- \nTesting the Tracer (Figure 7):\n%!";
  Printf.printf "----------------------------- \n%! ";
  let Ans afunc = test_tracer_on_ast (List.assoc option global_ast_map) in
  let _ans, MS (_o, n) = afunc init_state in ()
    
let _ =
  let option_list =  fst (List.split global_ast_map) in
  if Array.length Sys.argv = 3 && Sys.argv.(1) = "tracer" && (List.exists ((=) Sys.argv.(2)) option_list)
  then test Sys.argv.(2)
  else if Array.length Sys.argv > 1 && Sys.argv.(1) = "tracer" then
    begin
      Printf.printf "*** Please add a second option among : ";
      print_endline (String.concat ", " option_list);
      failwith "Not enough options"
    end;
  if Array.length Sys.argv = 2 && Sys.argv.(1) = "all" then
    test "hanoi"
