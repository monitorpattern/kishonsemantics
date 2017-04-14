open LlambdaAst
(** ---------------------------------------------------------------- 
    Examples
    ---------------------------------------------------------------- *)

(* factorial applied to five. *)
let ast_fact_five =
  Letrec ("fact",
          ("n",
           Cond (
             Eq (Id "n", Con (NAT 0)),
             Con (NAT 1),
             Mult (Id "n", App (Id "fact", Minus (Id "n", Con (NAT 1))))),
           App (Id "fact", Con (NAT 5))))

(* factorial applied to three with mult user-defined function .*)
let ast_ann_fact_five_mult =
  let ast_fact_ann =
    Letrec ("fact",
            ("n",
             AnnExpr (Ann "fact", Cond (
             Eq (Id "n", Con (NAT 0)),
             Con (NAT 1),
             App (App (Id "mult", Id "n"),  App (Id "fact", Minus (Id "n", Con (NAT 1)))))),
             App (Id "fact", Con (NAT 4))))
  in 
  Letrec ("mult",
          ("x",
           Lam ("y",  AnnExpr (Ann "mult" , Mult (Id "x", Id "y"))),
           ast_fact_ann))

(* The more we add annotations, the lower is the threshold over which a stack overflow occurs 
  Test with the naive 3 annotations on App fibo instead of the one wrapping the Cond. *)
let ast_ann_fibo =
  Letrec ("fibo",
          ("n",
           AnnExpr (Ann "fibo", Cond (
             Leq (Id "n", Con (NAT 1)),
             Id "n",
             (* Plus is a primitive operator *)
             Plus (  App (Id "fibo",  Minus (Id "n", Con (NAT 1)) ),
                     App (Id "fibo",  Minus (Id "n", Con (NAT 2)) ))
           )),
           App (Id "fibo", Con (NAT 21))))
(* fib 20 -> < 10946, 21890 > ; value : 6765
   fib 22 -> stack overflow
 *)

let global_ast_map = [
  ("fact", ast_fact_five);
  ("fact_ann", ast_ann_fact_five_mult);
  ("fibo_ann", ast_ann_fibo);
]
