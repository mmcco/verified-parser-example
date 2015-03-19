%{

Require Import String.

Inductive ast :=
    | OpExpr : string -> ast -> ast -> ast
    | Num : nat -> ast.

(* We make a type synonym to differentiate
   from nat extracted from other files. *)
Definition num : Type := nat % type.

%}

%token<num> NUM

(*
    This represents all operators. Giving each
    operator its own token probably would have
    been cleaner, but I wanted to include
    strings in the example.
*)
%token<string> OP

%token LPAREN RPAREN EOF

%type<ast> expr

%start<ast> top_expr
%%

top_expr:
    | e=expr EOF
        { e }

expr:
    | i=NUM
        { Num i }
    | LPAREN op=OP e1=expr e2=expr RPAREN
        { OpExpr op e1 e2 }
