{
    open Lexing
    open Printf
    open Specif
    open Parser
    (*open Main*)
    open Aut.GramDefs
    (*open Streams*)
    open BatString
    open String

    let rec of_int (n: int) : imm =
        assert (n >= 0);
        if n = 0 then O else S (of_int (pred n))

}

let letters = ['a' - 'z']+
let num = ['0' - '9']+
let whitespace = [' ' '\t' '\012' '\r']
let newline = '\n'


rule lex = parse
| letters as ls
    { get_token (OPCODE'tok (to_list ls)) }
| num as x
    { get_token (IMM'tok (of_int (int_of_string x))) }
| whitespace | newline
    { lex lexbuf }
| eof
    { get_token (EOF'tok ()) }

{
    let tokens_stream lexbuf : token stream =
        let rec compute_token_stream () =
            let loop c_exist =
                Cons (c_exist, Lazy.from_fun compute_token_stream)
            in loop (lex lexbuf)
        in
        Lazy.from_fun compute_token_stream
}
