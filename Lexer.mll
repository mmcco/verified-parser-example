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

    exception SyntaxError of string

    let rec of_int (n: int) : num =
        assert (n >= 0);
        if n = 0 then O else S (of_int (pred n))

}

let num = ['0' - '9']+
let whitespace = [' ' '\t' '\012' '\r']
let newline = '\n'
let op = "+" | "-" | "*" | "/" | "**"


rule lex = parse
| num as x
    { get_token (NUM'tok (of_int (int_of_string x))) }
| whitespace | newline
    { lex lexbuf }
| '('
    { get_token LPAREN'tok }
| ')'
    { get_token RPAREN'tok }
| op as op_str
    { get_token (OP'tok (to_list op_str)) }
| eof
    { get_token EOF'tok }
| _
    { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

{
    let tokens_stream lexbuf : token stream =
        let rec compute_token_stream () =
            let loop c_exist =
                Cons (c_exist, Lazy.from_fun compute_token_stream)
            in loop (lex lexbuf)
        in
        Lazy.from_fun compute_token_stream
}
