open LlambdaAnn
open Monitor

(** ------------------------------------------------------------------------
   Annotator : a function that annotates an AST from the llambda language
   --------------------------------------------------------------------------- *)
(* 
Fait: implementation d'un petit langage et de son extension pour un moniteur
- Construire un traceur pour le petit langage
- Construire un explorateur pour le petit langage
- Faire un generateur d'annotations dans un AST
- Ecrire un petit langage à la PIMCA : identifier le coeur minimal des concepts
- Implementer le profiler et le traceur avec le framework
*)

(* *)
let rec getFunctions e detectedNames = match e with
  | Con k -> detectedNames
  | Id i  -> detectedNames
  | Lam (arg, ebody) -> getFunctions ebody detectedNames
  | Cond (e1, e2, e3) ->
    (* GetFunctions nothing in condition *)
    let names1 = getFunctions e2 detectedNames in
    getFunctions e3 names1
  | App (e1, e2) -> getFunctions e1 (getFunctions e2 detectedNames)
  | Letrec (fname, (argname, e1, e2)) ->
    let names1 = getFunctions e1 (fname::detectedNames) in
    getFunctions e2 names1
  (* "Primitive" expressions *)
  | _ -> detectedNames

let test_annotator () =
  let functions = getFunctions (LlambdaAnn.ast0_fact) [] in
  Printf.printf "Functions to be annotated :\n";
  List.iter (fun f -> Printf.printf "%s;\n" f) functions

(**)
