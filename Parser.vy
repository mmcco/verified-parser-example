%{

Require Import String.
Require Tuples.

Inductive value :=
| Opcode : string -> value
| Imm : nat -> value.

Definition offset : Type := nat % type.
Definition imm : Type := nat % type.

%}

%token<string> OPCODE
%token<imm> IMM

%token EOF

%type<value> pval

%start<list value> pvals
%%

pvals:
| v = pval vs = pvals
    { v :: vs }
| v = pval EOF
    { v :: [] }

pval:
| o = OPCODE
    { Opcode o }
| i = IMM
    { Imm i }
