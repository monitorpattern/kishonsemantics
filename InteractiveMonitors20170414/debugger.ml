(* OCaml implementation of Fig. 22 
 - Todo : enable inChan and outChan to be real channels (stdin, stdout), 
   as well as file streams.
*) 
open LlambdaAst (* LDebug there *)
open LlambdaAlg 
open LlambdaInt
open Fixpoint
open Printf
(** ----------------------------------------------------------------
    Making explicit the "instantiation" of types (Answer type) for the
    debugger.
    ------------------------------------------------------------------ *)   

(* --- Answer Algebra --- *)

type 'monState debugAns = ('monState -> IO.inChannel -> (IO.inChannel * IO.outChannel)) ans
   
let phi = fun v -> Ans (Printf.sprintf "[Phi] result is: %s%!\n" (string_of_denval v))
let over_phi = fun x ->
  (* theta : answer transformer.
     Transforms an answer into a pair <answer, monitor state>. *)
  let theta (Ans ans) = fun ms (inChan:IO.inChannel) -> inChan, ans in
  Ans (theta (phi x))

(** ----------------------------------------------------------------
   MONITOR SYNTAX
   ------------------------------------------------------------------ *)

(* --- see llambdaAst.ml, the type extension of 'm ann. --- *)

(* string of annotation ... *)
let string_of_expr x =
  let string_of_ann = function
    | LBreak -> ""
    | LDebug (fName, fargs, lvars) ->
      Printf.sprintf "LDebug (%s, args:%s, lvars:%s):" fName (String.concat "," fargs)
        (String.concat "," lvars)
  in LlambdaAst.string_of_ann_expr string_of_ann x
(** ----------------------------------------------------------------
   MONITOR ALGEBRAS (Fig. 22, part 1)
   ------------------------------------------------------------------ *)
  
(* -- TYPES -- *)
    
open LlambdaExt (* Primitive types for interpreter data handling (env, store, etc.) *)
type frame = (string * string list * string list)       
type monState = (string setType * frame stackType * bool)
type iostate = (IO.inChannel * IO.outChannel * monState)
    
(* -- OPERATIONS -- *)
(* Updaters for debug state *)
let updStp stp ( _, stk, brk) = (stp, stk, brk) 
let updBrk brk ( stp, stk, _) = (stp, stk, brk)
let updStk stk ( stp, _, brk) = (stp, stk, brk)
(* FIXME hacky *)
let writeUsr msg = match msg with
  |  "command? " -> Printf.printf "%s" msg ; "\n"
  | _ -> print_endline msg ; msg ^ "\n"
(* let writeUsrNoend msg = Printf.printf "%s" msg ; msg *)

    
(* Handle the case where the user enter a non secable request 
e.g. debug (fac 0) -> (fac 0) cannot be split *)
let readUsr inChan = (** return: (usrInput, inChan') *)
  if String.length inChan = 0 then (* If input is consumed *)
    let res = read_line () in IO.split res 
  else    
    let (currUsrInput, inChan') =  IO.split inChan in
    Printf.printf "cmd: %s\n" currUsrInput;
    (currUsrInput, inChan')
      
(* getCmd exp semArgs input debuggerState : (bool, input) where input is user req. *)  
let rec getCmd e rho inp dstate =
  let out1 = writeUsr "command? " in
  let (cmd, inp1) = readUsr inp in
  let (resume, (inp2, out2, dstate2)) = processCmd cmd e rho inp1 dstate in  
  let (inp3, out3, dstate3) =
    if resume then (inp2, IO.emptyOut, dstate2)
    else getCmd e rho inp2 dstate2 in
  (* (inp3, LlambdaAlg.IO.concatList [out1;out2;out3], dstate3) *)
  (inp3, IO.emptyOut, dstate3)

(* dstate : 
- 1st element: contains the list of breakpoints - steps
- 2nd element: the frame stack*)
and processCmd cmd e rho inp ((stp, stk, brk) as dstate) =
  (match cmd with
    | "run" -> (true, (inp, IO.emptyOut, dstate))
  (* perform a single interpretive step *)
    | "step" ->

    (try 
       let (fn, fvars, lvars) = stkTop stk in
      let out1 = writeVars "formal " fvars rho in
      let out2 = writeVars "local " lvars rho in
      Printf.printf "step?:%s." (IO.concat out1 out2)
     with _emptyStack ->
       Printf.printf "step:EMPTY STACK\n"
    );      
      (true, (inp, writeUsr (string_of_expr e), updBrk true dstate))
  (* display the next expr to be evaluated *)
  | "list" -> (false, (inp, writeUsr (string_of_expr e), dstate))
  (* stop execution when requested function is called *)
  | "stop" ->
    let fn, inp1 = readUsr inp in
    (false, (inp1, IO.emptyOut, updStp (setInsert fn stp) dstate))
  (* delete breakpoint at requested function *)
  | "unstop" ->
    let fn, inp1 = readUsr inp in
    (false, (inp1,IO.emptyOut, updStp (setDelete fn stp) dstate))
  (* display the formal and local args of current functions *)
  | "show" ->
    (try 
       let (fn, fvars, lvars) = stkTop stk in
       Printf.printf "EMPTY STACK???...%s\n" (String.concat ";" lvars);
      let out1 = writeVars "formal " fvars rho in
      let out2 = writeVars "local " lvars rho in
      (false, (inp, IO.concat out1 out2, dstate))
     with _emptyStack ->
       Printf.printf "EMPTY STACK...\n";
      (false, (inp, "<emptyStack>", dstate)))
 (* Evaluate with current dynamic environment *)
  | "eval" -> (false, recDebug rho inp dstate false)
 (* Debug with current dynamic environment *)
  | "debug" -> (false, recDebug rho inp dstate true)
  (* display the current function call chain *)
  | "where" ->
    let fns = String.concat ";" (List.map (fun (fn,_,_) -> fn) stk) in
      (false, (inp, writeUsr fns, dstate))
  | s -> false, (inp, writeUsr (sprintf "<undefined command : %s>" s), dstate))

(* (Fig. 22 part-two) *)
and recDebug rho inp dstate isDebug =
  (* V0 : hard coded *)
  let (exp, inp1) = readUsr inp in (*readUsr "" in*)
  let ast = Loader.parseString exp in
  let  Ans f =  (FixNative.fix (over_g_lambda monitor_pre monitor_post)) ast
    rho (fun v -> over_phi v)
  in
  (* (inp2, out2) *)
  let inp2out2 = f (setEmpty, stkEmpty, isDebug) in 
  (* Attention, en haskell comp. ++ dans recDebug -- inChannel/outChannel*)
  let out3 =
    if isDebug then
      begin
        let msg_pre = writeUsr ">> Enter Recursive Debug%!" in
        let out2 = snd (inp2out2 inp) in (* Input empty in recDebug *)
        let msg_post = writeUsr ">> Exit Recursive Debug%!" in
        IO.concatList [
          msg_pre; out2; (* Inputs... *) msg_post ]
      end
    else
       let out2 = snd (inp2out2 inp) in out2

  in (fst (inp2out2 inp), out3, dstate)

    
and writeVars prefix ids rho =
  match ids with
   | [] -> IO.emptyOut
   | id::rest ->
     let out = writeUsr (IO.concatList [prefix; id; " := "; getIdVal rho id]) in
     let stk = writeVars prefix rest rho in
     ""
     
and getIdVal rho id =
  try string_of_denval (access_rho id rho)
  with anon_failure -> "<undef value>"

and writeTrace rho stk =
  let (fn, fargs, _) = stkTop stk in
  let stk = writeUsr (IO.concat "Stop in " fn) in
  let out = writeVars "Formal argument " fargs rho in
  ""
  (* IO.concat stk out *)
                              
    
(** ------------------------------------------------------------------
   MONITORING FUNCTIONS 
    ------------------------------------------------------------------ *)

(* [JFP] rho => semArgs ; sigma => monState/dstate ; ann => label *)

and monitor_pre ann e rho (((stp, stk, brk) as dstate):monState)
    : (IO.inChannel -> (IO.inChannel * IO.outChannel * monState))=
  fun inp ->
    match ann with
      (* Next state, we don't interrupt? *)
      | LBreak ->
        if brk then getCmd e rho inp (updBrk false dstate)
        else (inp, IO.emptyOut, dstate)
      | LDebug (fn, fvars, lvars) ->
        (* Z comment : the stack is artificially built (instead of debugging
           a program under abstract machine, one debug under interpretation but shows
           an abstract-machine state...? *)
        let stk' = stkPush (fn, fvars, lvars) stk in
        let dstate' = updStk stk' dstate in
        if setMember fn stp then
          (inp, writeTrace rho stk', updBrk true dstate')
        else 
          (inp, IO.emptyOut, dstate')
        
and monitor_post ann e rho v ((stp, stk, brk) as dstate)
    : (IO.inChannel -> (IO.inChannel * IO.outChannel * 'monState)) =
  fun inp ->      
    match ann with
      | LBreak -> (inp, IO.emptyOut, dstate)
      | LDebug (fn, fvars, lvars) ->
        (inp, IO.emptyOut, updStk (stkPop stk) dstate)

(** ----------------------------------------------------------------
    Top-level function
   ------------------------------------------------------------------ *)   

(* This top level function amounts in JFP to the execute function
   applied to a combined monitor and interpreter 
   expr -> newAns kont -> newAnsans = <fun>
   where newAns = (monState -> IO.inChannel -> IO.inChannel * IO.outChannel)
*)
let interpreter inputRequests expr (monitor_pre, monitor_post, monitor_state) =
  let Ans f = (FixNative.fix (over_g_lambda monitor_pre monitor_post)) expr
    empty_env (fun v -> over_phi v) in
  (* last parameter is the initial input channel *)
  f monitor_state inputRequests

(* TODO : define a IOMonitor module - as done in Haskell with IOMonitorType  *)
(** The "debugger" variable simply groups the monitor functions needed for
    the debug-monitor : 
     - Annotation function
     - Pre-monitor function
     - Post-monitor function
     - Initial monitor state which value is (setEmpty, stkEmpty, true) 
*)
let debugger = (LlambdaAst.annotate_letrec,
                monitor_pre,
                monitor_post, (setEmpty, stkEmpty, true))

(* TODO : define a IOMonitor module - as done in Haskell with IOMonitorType *)
let (<$>) monitorSpec evalSpec = fun expr ->
  let (ann_fun, pre, post, monState) = monitorSpec in
  Printf.printf "[<$>] %s\n%!" (string_of_expr (ann_fun expr));
  evalSpec (ann_fun expr) (pre, post, monState)
  
(** ----------------------------------------------------------------
    Unit Tests
   ------------------------------------------------------------------ *)   
let test1_simpleFact3 () =
  (* Runs the debugger with a set of predefined requests to gain time *) 
  let simpleFact3::_ = Loader.parse "Tests/testUnit_simpleFact3.llambda" in
  let demo_interpreter = interpreter
    "stop fac run show run where step list step run run run run" (* unstop fac run *) in  
  (debugger <$> demo_interpreter) simpleFact3

let test2_simpleFact3 () =
  (* Runs the debugger with a set of predefined requests to gain time *) 
  let simpleFact3::_ = Loader.parse "Tests/testUnit_simpleFact3.llambda" in
  let demo_interpreter = interpreter
    ("stop fac run show run where step list eval n " 
     ^ "unstop fac run") in  
  (debugger <$> demo_interpreter) simpleFact3


let test3_simpleFact3 () =
  (* Runs the debugger with a set of predefined requests to gain time *) 
  let simpleFact3::_ = Loader.parse "Tests/testUnit_factacc.llambda" in
  let demo_interpreter = interpreter
    ("stop fac run show run where step list eval n" 
     ^ " debug (fac 0) stop fac run step list step step step list step"
     ^ " unstop fac run ") in  
  (debugger <$> demo_interpreter) simpleFact3

let teststdin (filename:string) =
  let expr::_ = Loader.parse filename in
  let demo_interpreter = interpreter "BONJOUR" in (* "BONJOUR" : empty request *) 
  (debugger <$> demo_interpreter) expr

    
let test4_factmult () =
  teststdin "Tests/testUnit_factmult.llambda"
    
let teststdin_simpleFact3 () =
  (* Runs the debugger with a set of predefined requests to gain time *) 
  let simpleFact3::_ = Loader.parse "Tests/testUnit_factacc.llambda" in
  let demo_interpreter = interpreter "" in  
  (debugger <$> demo_interpreter) simpleFact3
    
let test_simpleFact5 () =
  let simpleFact5 = LlambdaAstExamples.ast_fact_five in
  (debugger <$> (interpreter IO.emptyIn)) simpleFact5

let global_test_map = function 
  | "1" -> test1_simpleFact3
  | "2" -> test2_simpleFact3
  | "3" -> test3_simpleFact3
  | "4" -> test4_factmult
  | "stdin" -> teststdin_simpleFact3
  | _ -> failwith "Unvalid argument. Choose: 1, 2, 3, or stdin"
    
(** ----------------------------------------------------------------
    Main
  ------------------------------------------------------------------ *)
    
let _ =  
  if Array.length Sys.argv = 2 then
    begin
      let line () = Printf.printf "-------------------------------------- \n" in
      line (); Printf.printf "Testing the Interactive Debugger:\n"; line ();
      global_test_map (Sys.argv.(1)) ();
      ()
    end
  else if Array.length Sys.argv = 3 && Sys.argv.(1) = "stdin" then
    begin
      
      teststdin Sys.argv.(2);
      ()
    end
  else   
    Printf.printf "Missing argument 1, 2, 3 or stdin [filename]\n"






                                 
