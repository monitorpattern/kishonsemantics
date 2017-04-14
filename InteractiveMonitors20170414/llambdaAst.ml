(** ----------------------------------------------------------------
   Abstract Syntax
   ----------------------------------------------------------------
   Notes: 'm is the type of Monitor State, "instantiated" when a
   monitor function is attached to the language evaluator.
   ------------------------------------------------------------------ *)
type con = BOOL of bool | NAT of int | LIST of int list
type  id = string
type 'm ann = ..
type  'm ann += Ann of 'm
    
(** ----------------------------------------------------------------
    Abstract Syntax
    ---------------------------------------------------------------- *)
 
type  'm expr  = ..
type  'm expr +=
  | Unit (* To fake a letrec without arguments *)
  | Con of con
  | Id of id
  | Lam of id *  'm expr
  | Cond of  'm expr *  'm expr *  'm expr
  | App of  'm expr *  'm expr
  | Letrec of id * (id *  'm expr *  'm expr)
  | Let of id * 'm expr * 'm expr
  | Succ of  'm expr

(* "Primitive" 'm expressions *)
type 'm expr +=
  | Leq of  'm expr *  'm expr
  | Eq of  'm expr *  'm expr
  | Plus of 'm expr * 'm expr
  | Minus of  'm expr *  'm expr
  | Mult of  'm expr *  'm expr
  | Div of 'm expr * 'm expr
  | Mod of 'm expr * 'm expr
(* Primitive list expressions *)
type 'm expr +=
  | Tail of id
  | Head of id
  | Cons of 'm expr * id  

type 'm expr += AnnExpr of 'm ann * 'm expr

(** ----------------------------------------------------------------
    [Interactive debugging-specific] Abstract Syntax
    ---------------------------------------------------------------- *)
(* LDebug funName argList *)
type 'm ann += LBreak | LDebug of string * string list * string list
        

(** ----------------------------------------------------------------
    AST String conversion function
    ---------------------------------------------------------------- *)    
let string_of_expr_fun self = function
    | Unit -> "unit"
    | Con c -> (match c with BOOL b -> string_of_bool b | NAT i -> string_of_int i | LIST l -> "[" ^ String.concat ";"  (List.map string_of_int l) ^ "]")
    | Id i ->  i 
    | Lam (i, e) -> "fun " ^ i ^ " -> " ^ (self e)
    | Cond (ec, e1,e2) -> "if " ^ (self ec) ^ " then " ^ (self e1) ^ " else " ^ (self e2)
    | App (e1, e2) -> "[App]" ^ (self e1) ^ " " ^ (self e2) ^ " " 
    | Letrec (i , (i_arg, e1, e2)) -> "letrec " ^ i ^ " " ^ i_arg ^ " = "  ^ (self e1) ^ " in\n" ^ (self e2)
    | Let (i, e1, e2) -> "let "^i ^ " = " ^ (self e1) ^ " in\n" ^ (self e2)
    | Succ e -> "(" ^ (self e) ^ " + 1)"
    | Leq (e1,e2) -> "(" ^ (self e1) ^ " <= " ^ (self e2) ^ ")"
    | Eq (e1,e2) -> "(" ^ (self e1) ^ " = " ^ (self e2)^ ")"
    | Plus (e1,e2) -> "(" ^ (self e1) ^ " + " ^ (self e2)^ ")"
    | Minus(e1,e2) -> "(" ^ (self e1) ^ " - " ^ (self e2)^ ")"
    | Mult(e1,e2) -> "(" ^ (self e1) ^ " * " ^ (self e2)^ ")"
    | Div(e1,e2) -> "(" ^ (self e1) ^ " / " ^ (self e2)^ ")"
    | Mod(e1,e2) -> "(" ^ (self e1) ^ " mod " ^ (self e2)^ ")"
    | Tail i -> "tail " ^ i
    | Head i -> "head " ^ i
    | Cons (e, i) -> " (" ^ (self e) ^ ")::" ^ i
    | AnnExpr (a, e) -> (self e)

let string_of_expr e = Fixpoint.FixNative.fix string_of_expr_fun e   (*fun-fun*)

 (* an "inheritance" mechanism : enabling any annotation by passing
the specific-annotation printer. *)
let string_of_ann_expr string_of_ann e =
  let str_of_ann self e = match e with
  | AnnExpr (a, e) -> (string_of_ann a) ^ (self e)
  | _ -> (string_of_expr_fun self e)
  in Fixpoint.FixNative.fix str_of_ann e

let string_of_ann_expr2 string_of_ann e =
  let str_of_ann self e = match e with
    | AnnExpr (a, e) -> (string_of_ann a) ^ (self e)
    | App _ -> "[App]" ^ (string_of_expr_fun self e)
    | Let _ -> "[Let]" ^ (string_of_expr_fun self e)
    | Minus _ -> "[-]" ^ (string_of_expr_fun self e)
    | Plus _ -> "[+]" ^ (string_of_expr_fun self e)            
    | _ -> (string_of_expr_fun self e)
  in Fixpoint.FixNative.fix str_of_ann e

  
(* FIXME Subtimal incomplete annotation functions -- to put elsewhere *)
let rec get_localvars expr = match expr with
  | Letrec (id, (idv, body, app)) ->
    (get_localvars body)@(get_localvars app)
  | Let (id, body, app) ->
    id::(get_localvars body)@(get_localvars app)
  | App (e1, e2) ->
    (get_localvars e1)@(get_localvars e2)
  | Cond (ec, e1,e2) -> (get_localvars ec)@(get_localvars e1)@(get_localvars e2)
  | Lam (id, e) -> get_localvars e
  | _ -> []

let rec get_formalargs expr = match expr with
  | Letrec (id, (idv, body, app)) ->
    idv::((get_formalargs body)@(get_formalargs app))
  | Let (id, body, app) ->
    (get_formalargs body)@(get_formalargs app)
  | App (e1, e2) ->
    (get_formalargs e1)@(get_formalargs e2)
  | Cond (ec, e1,e2) -> (get_formalargs ec)@(get_formalargs e1)@(get_formalargs e2)
  | Lam (id, e) -> id::(get_formalargs e)
  | _ -> []
      
let initAssocList = []
let accessAssocList i l =
  if List.mem_assoc i l then List.assoc i l else []
let updateAssocList i v l =
  let vl = accessAssocList i l in
  let l' = (List.remove_assoc i l) in
  (i,v::vl)::l'
    
(* Maintain a list of formal vars for each function definition through
   letrec , include lam variables
   acc : assocList
   FIXME : dirty annotation function for test purpose only
*)
let annotate_letrec expr =
  let formalargs = get_formalargs expr
  and localvars = get_localvars expr in
  let rec ann_rec expr embeddingfun =
    match expr with
      | Letrec (id, ((idv, body, app) as letrecBody)) ->
        Letrec (id, (idv, AnnExpr (
          LDebug (id, formalargs, localvars), ann_rec body id),
                      AnnExpr (LDebug (id, formalargs, localvars), app) ))
    | _ -> expr
  in ann_rec expr ""
      
      


      
