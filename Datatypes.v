Require Import String.
Require Import Parser.

Inductive token_inductive :=
    | EOF'tok : unit -> token_inductive
    | IMM'tok : nat -> token_inductive
    | OPCODE'tok : string -> token_inductive.

Definition get_token (ti : token_inductive) : Aut.GramDefs.token :=
    match ti with
        | EOF'tok u =>
            {Gram.EOF't:Gram.terminal & unit}
        | IMM'tok n =>
            {t:Gram.IMM't & n}
        | OPCODE'tok str =>
            {t:Gram.OPCODE't & str}
    end.
