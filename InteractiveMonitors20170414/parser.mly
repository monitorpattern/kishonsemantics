(*  
   Description: 
    A Basic parser for a miniML language
    This code was picked and adapted from the web to gain time in code writing... 
    Source: http://andrej.com/plzoo/html/miniml.html 
*)


%{
  open LlambdaAst
%}

%token IN
%token TINT
%token TBOOL
%token TARROW
%token <string> VAR
%token <int> INT
%token TRUE FALSE
%token PLUS
%token MINUS
%token TIMES DIV MOD
%token EQUAL LEQ 
%token IF THEN ELSE
%token FUN IS
%token COLON
%token LPAREN
%token RPAREN
%token LET LETR
%token SEMICOLON2
%token SUCC
%token EOF

%start toplevel
%type <'m LlambdaAst.expr list> toplevel

%nonassoc FUN IN 
%nonassoc IF THEN ELSE 
%nonassoc EQUAL LEQ
%left VAR
%left PLUS MINUS 
%right TARROW
%left TIMES DIV MOD
%left COLON
%%

toplevel:
 (* Z-FIXME : check if this list of rules is really necessary for making the parsing unambiguous. *)
| statements=list(expr) EOF                 { statements }

expr:
  | non_app             { $1 }
  | app                 { $1 }
  | arith               { $1 }
  | boolean             { $1 }
  | FUN id=VAR TARROW e=expr   { Lam(id, e) }
  | IF expr THEN expr ELSE expr        { Cond ($2, $4, $6) }
  | LETR funName=VAR id=VAR EQUAL e1=expr IN e2=expr { Letrec (funName, (id, e1, e2)) }
  | LET varName=VAR EQUAL e1=expr IN e2=expr { Let (varName, e1, e2) } 

    
app:
 | app non_app         { App ($1, $2) }
 | non_app non_app     { App ($1, $2) } 
            
non_app:
  | VAR                           { Id $1 }
  | TRUE                          { Con (BOOL true) }
  | FALSE                         { Con (BOOL false) }
  | INT                           { Con (NAT $1) }
  | LPAREN expr RPAREN { $2 } (* Must be put here: if defined in expr, ambiguous? *)


arith:
  | expr PLUS expr       { Plus ($1, $3) }
  | e1=expr MINUS e2=expr    { Minus (e1, e2) }
  | expr TIMES expr      { Mult ($1, $3) }
  | expr DIV expr        { Div ($1, $3) }
  | expr MOD expr        { Mod ($1, $3) }
  | SUCC expr            { Succ $2 }

      
boolean:
  | expr EQUAL expr { Eq ($1, $3) }
  | expr LEQ expr  { Leq ($1, $3) }

      
%%

