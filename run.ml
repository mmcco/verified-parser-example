open Array
open Sys
open Lexing
open Lexer
open Parser
open Parser.Inter

let _ =
    let rec inf = S inf in

    let cin =
      if Array.length Sys.argv > 1
      then open_in Sys.argv.(1)
      else stdin
    in
    let lexbuf = Lexing.from_channel cin in
    (match top_expr inf (Lexer.tokens_stream lexbuf) with
        | Fail_pr ->
                print_endline "failed!"
        | Timeout_pr ->
                print_endline "timed out!"
        | Parsed_pr (output, _) ->
                print_endline "worked!")

