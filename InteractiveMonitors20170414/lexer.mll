(*  
   Description: 
    A Basic parser for a miniML language
    This code was picked and adapted from the web to gain time in code writing... 
    Source: http://andrej.com/plzoo/html/miniml.html 
*)

{
  open Parser
  exception Error of string

}

let var = ['a'-'z' 'A'-'Z' '_' '+' '-']['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule token = parse
    [' ' '\t' '\r' '\n'] { token lexbuf }
  | '-'?['0'-'9']+           { INT (int_of_string(Lexing.lexeme lexbuf)) }
  | "int"                { TINT }
  | "bool"               { TBOOL }
  | "true"               { TRUE }
  | "false"               { FALSE }
  | "fun"           { FUN }
  | "is"            { IS }
  | "if"            { IF }
  | "then"          { THEN }
  | "else"          { ELSE }
  | "let"           { LET }
  | "letrec"        { LETR }
  | "in"            { IN }
  | ";;"            { SEMICOLON2 }
  | '='             { EQUAL }
  | "<="             { LEQ }
  | "->"            { TARROW }
  | ':'             { COLON }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | '+'             { PLUS }
  | "succ"            { SUCC }
  | '-'             { MINUS }
  | '*'             { TIMES }
  | '/'             { DIV }
  | "mod"           { MOD }
  | var             { VAR (Lexing.lexeme lexbuf) }
  | eof             { EOF }
  (* comment *)
  | "#" [^ '\n' '\r']* { token lexbuf }      
  | _             { raise (Error (Printf.sprintf "[LlambdaInt] At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }


{
}
