Require Parser.
Require Datatypes.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction Language Ocaml.

Extraction "Main.ml" Main.Make.
Extraction "Parser.ml" Parser.pvals Datatypes.get_token Parser.imm.
