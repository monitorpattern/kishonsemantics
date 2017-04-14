open Fixpoint
open LlambdaAnn


(** ----------------------------------------------------------------
    Examples
    ------------------------------------------------------------------ *)
let ast0_minus =
  Letrec ("minus",
          ("n", Minus (Con (NAT 0), Id "n"),
           App (Id "minus", Con (NAT 42))))
(* Weird addition for test purpose... *)
let ast0_plus =
  Letrec ("plus",
          ( "n",
            Lam ("m", Cond (Eq (Id "m", Con (NAT 0)),
                            Id "n",
                            App (App (Id "plus",
                                      Succ (Id "n")), Minus(Id "m", Con (NAT 1))))),
            App (App (Id  "plus", Con (NAT 10)),
                 Con (NAT 11))))
(* Factorial 10 = 3628800 *)  
let ast0_fact = Letrec ("fact",
                        (  "n",
                           Cond (
                             Eq (Id "n", Con (NAT 1)),
                             Con (NAT 1),
                             Mult (Id "n",  App (Id "fact", Minus (Id "n", Con (NAT 1))))
                           ),
                           App (Id "fact", Con (NAT 10))))
(* Fibonacci 14 = 377 *)
let ast0_fibo =
  Letrec ("fibo",
          ("n",
           Cond (
             Leq (Id "n", Con (NAT 1)),
             Id "n",
             (* Plus operator : implicit Application *)
             Plus ( App (Id "fibo",  Minus (Id "n", Con (NAT 1)) ),
                    App (Id "fibo",  Minus (Id "n", Con (NAT 2)) ))
           ),
           App (Id "fibo", Con (NAT 25))))
(* Fibonacci without naming it (not printable :-P) *)
let ast0_fibo_lam =
  let rec lam_fun = Lam ("n",
                         Cond (
                           Leq (Id "n", Con (NAT 1)),
                           Id "n",
         (* Plus operator : implicit Application *)
                           Plus ( App (lam_fun,  Minus (Id "n", Con (NAT 1)) ),
                                  App (lam_fun,  Minus (Id "n", Con (NAT 2)) ))
                         ))
  in App (lam_fun, Con (NAT 25))

(** ----------------------------------------------------------------
    Main
    ------------------------------------------------------------------ *)
(* Page 7 : std *)
let k_init_str = k_init_param (fun v -> Printf.printf "The result is %s\n%!" (string_of_denval v))

  
let test () =
  Printf.printf "\n----------------------------- \nTesting the Semantics:\n";
  Printf.printf "----------------------------- \n";
  Printf.printf "\nFactorial: %s\n" (string_of_expr ast0_fact);
  (FixNative.fix g_lambda) ast0_fact empty_env k_init_str;
  Printf.printf "\nAddition of 10 and 11: ";
  (FixNative.fix g_lambda) ast0_plus empty_env k_init_str;
  Printf.printf "\nFibonacci: %s\n" (string_of_expr ast0_fibo);
  (FixNative.fix g_lambda) ast0_fibo empty_env k_init_str;
  (FixNative.fix g_lambda) ast0_fibo_lam empty_env k_init_str;
  ()

let help () =
  let ic = open_in "help.txt" in
  let n = in_channel_length ic in
  let s = String.create n in
  really_input ic s 0 n;
  close_in ic;
  Printf.printf "%s%!" s

let _ =
  let options = ["all"; "semantics"; "tracer"; "demon"; "demon2"; "collector"; "profiler"; "profiler2"] in
  Printf.printf "\n === Tests started from llambdaTests.ml ===\n";
  if (Array.length Sys.argv > 1) && (Sys.argv.(1) = "all" || Sys.argv.(1) = "semantics") then
    test ()
  else if (Array.length Sys.argv = 1) ||
      (Array.length Sys.argv > 1 && List.exists ((<>) Sys.argv.(1)) options) then
    help ()
