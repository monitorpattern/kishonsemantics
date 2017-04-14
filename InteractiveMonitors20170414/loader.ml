open Lexing
open Parser
open Lexer
open Printf

let parse filename =
  printf "[loader.ml] Parsing %s ... \n" filename ;
  (* Open the file mtx.confs to parse *)
  let input = open_in filename in
  (* Create a stream for this file *)
  let filebuf = Lexing.from_channel input in
  
  try
   (* Parse the stream given the grammar defined in Parser and Lexer *)
    let astCode= Parser.toplevel Lexer.token filebuf in
    Printf.printf "[loader.ml] Done.\n";
    astCode
  with
    | Lexer.Error msg ->
      Printf.eprintf "Unknown token: %s%!" msg ; failwith "Lex error"
    | Parser.Error ->
    Printf.eprintf "At offset %d: syntax error. 
Get position with :  head -c <line-offset> <filename>
\n%!" (Lexing.lexeme_start filebuf) ;
    failwith (Printf.sprintf "At offset %d: syntax error.\n%!" (Lexing.lexeme_start filebuf))

let parseString inputString =
  let filebuf = Lexing.from_string inputString in
  
  try
   (* Parse the stream given the grammar defined in Parser and Lexer *)
    let astCode::_ = Parser.toplevel Lexer.token filebuf in
    astCode (* FIXME : make explicit that a single statement is expected *)
  with
    | Lexer.Error msg ->
      Printf.eprintf "Unknown token: %s%!" msg ; failwith "Lex error"
    | Parser.Error ->
    Printf.eprintf "At offset %d: syntax error. 
Get position with :  head -c <line-offset> <filename>
\n%!" (Lexing.lexeme_start filebuf) ;
    failwith (Printf.sprintf "At offset %d: syntax error.\n%!" (Lexing.lexeme_start filebuf))

