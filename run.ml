open Array
open Sys
open Lexing
open Lexer
open Main

let _ =
    let rec inf = Parser.S inf in

    let cin =
      if Array.length Sys.argv > 1
      then open_in Sys.argv.(1)
      else stdin
    in
    let lexbuf = Lexing.from_channel cin in
    (match Parser.pvals inf (Lexer.tokens_stream lexbuf) with
        | Parser.Parser.Fail_pr ->
                print_endline "failed!"
        | Parser.Parser.Timeout_pr ->
                print_endline "timed out!"
        | Parser.Parser.Parsed_pr (output, _) ->
                print_endline "worked!")

