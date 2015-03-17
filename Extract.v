Require Parser.
Require Datatypes.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction Language Ocaml.

Extraction "Main.ml" Main.Make.
Extraction "Parser.ml" Parser.top_expr Datatypes.get_token Parser.num.
