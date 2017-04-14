(** ----------------------------------------------------------------
 * Paper experiment: 
 *   Monitoring Semantics : A Formal framework for Specifying, Implementing,
 *   and Reasoning about Execution Monitors.
 *   + JFP Semantics Directed Program Execution Monitoring - Authors: Kishon & Hudak
 * 
 * Description:
 *    Faithfull implementation of the JFP's annex A
 *      (Haskell Support Code... in OCaml)
 *
 *    Contains the internal structures for debugging (frame stack, env...)
 *    Most of them are just wrappers of ocaml list functions and
 *    are defined to match the original source code from Kishon/Hudak journal
 * ---------------------------------------------------------------- **)

(** ----------------------------------------------------------------
   Standard Algebra
   ------------------------------------------------------------------ *)  

(* -- STACKS -- *)
type 'a stackType = 'a list
let stkEmpty = []
let stkPush x s = x::s
let stkPop = function (_::s) -> s | [] -> failwith "pop:Stack is empty"
let stkTop = function (x::_) -> x | [] -> failwith "top:Stack is empty" 
let rec string_of_stk = function
  | [] -> ""
  | (fn, fvars, lvars)::r ->
    "fun " ^ fn ^ ":" ^ (String.concat " " fvars) ^ (String.concat " " lvars) ^
      "\n" ^ (string_of_stk r)
    
(* -- SETS -- *)
type 'a setType = 'a list
let setEmpty = []
let rec setMember x = function
  | [] ->  false
  | y::s -> if (x = y) then true else setMember x s
let rec string_of_set = function
  | [] -> ""
  | x::xs -> x^" "^(string_of_set xs)
    
let setInsert x xs = if List.for_all ((<>) x) xs then x::xs else xs
let setDelete x xs = List.filter ((<>) x) xs
        
(* -- ASSOC LISTS -- *)
type ('a, 'b) assocType = ('a * 'b) list
let assocEmpty = []
let assocPut id x l = if List.mem_assq id l then l else (id, x)::l
let assocGet id l = List.assoc id l
let assocExist id l = List.mem_assoc id l

(* -- ENVIRONMENTS -- *)
type ('k, 'v) envType = 'k -> 'v
let envEmpty = fun i -> failwith "Empty"
let envUpd env id v = fun i -> if i = id then v else env i

(* -- STORES -- *)
type loc = int
type 'storeableVal storeType = loc * ((loc , 'storeableVal) envType)
let storeEmpty undefVal = (1, envEmpty undefVal)
let storeLook (l, env) loc = env loc
let storeUpd (l, env) loc v = (l, envUpd env loc v)
let storeAlloc (l, env) = (l , (l+1, env))


    


  
