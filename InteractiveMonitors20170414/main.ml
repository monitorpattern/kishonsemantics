open LlambdaAst
open LlambdaAlg
open Printf

let test filename =
  Printf.printf "[main.ml] Main program execution\n";
  (* Load a file and get its AST. *)
  let astCode = Loader.parse filename
  in
  Printf.printf "File '%s' : Parse done.\n" filename; 
  Printf.printf "%s\n" (String.concat "\n"
                        (List.map (fun ast -> LlambdaAst.string_of_expr ast) astCode));
  Printf.printf "[main.ml] END.\n"

        (* Help for parse error : head -c <line-offset> *)

let fileList =
  ["Tests/testUnit_factorial.llambda";
   "Tests/testUnit_app.llambda";
   "Tests/testUnit_factmult.llambda"
  ]

let allTests () =
  List.iter (fun fName -> test fName) fileList;
  Loader.parseString "(fac 0)";
  Printf.printf "End of tests in main.ml\n"

let _ =
  if (Array.length Sys.argv = 2) then
    if Sys.argv.(1) = "parse" then allTests()

      
