{
    open Lexing
    open Printf
    open Specif
    open Parser
    open Aut.GramDefs
    open Streams

    let tok v t =
        Coq_existT (t, Obj.magic v)
}

let letters = ['a' - 'z']
let num = ['0' - '9']
let whitespace = [' ' '\t' '\012' '\r']
let newline = '\n'


rule lex = parse
| letters as ls
    { tok OPCODE't ls }
| num as x
    { tok IMM't x }
| whitespace | newline
    { lex lexbuf }
| eof
    { tok EOF't () }

{
    let tokens_stream lexbuf : token coq_Stream =
        let rec compute_token_stream () =
            let loop c_exist =
                Cons (c_exist, Lazy.from_fun compute_token_stream)
            in loop (lex lexbuf)
        in
        Lazy.from_fun compute_token_stream
}
