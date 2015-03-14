{
    open Lexing
    open Printf
    open Specif
    open Parser
    open Aut.GramDefs
    open Streams

    let tok v t =
        Coq_existT (t, v)
}

let letters = ['a' - 'z']+
let num = ['0' - '9']+
let whitespace = [' ' '\t' '\012' '\r']
let newline = '\n'


rule lex = parse
| letters as ls
    { tok OPCODE't (Obj.magic ls) }
| num as x
    { tok IMM't (Obj.magic (int_of_string x)) }
| whitespace | newline
    { lex lexbuf }
| eof
    { tok EOF't (Obj.magic ()) }

    (*
{
    let tokens_stream lexbuf : token stream =
        let rec compute_token_stream () =
            let loop c_exist =
                Cons0 (c_exist, Lazy.from_fun compute_token_stream)
            in loop (lex lexbuf)
        in
        Lazy.from_fun compute_token_stream
}
*)
