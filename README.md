# verified-parser-example
A minimal example of a formally verified parser using ocamllex and Menhir's Coq
backend.

This would seem to be simpler than it is, as the interaction between the lexer
(directly generated OCaml) and the parser (OCaml extracted from generated Coq)
is nonobvious, not standardized, and generally undocumented.

## Requirements

* Coq
* OCaml (with ocamlfind and ocamllex, which should be included)
* the OCaml Batteries library
* Menhir

## On the parser

A Coq backend (using the `--coq` flag) was recently added to Menhir. It
originated in and is used by [CompCert](http://compcert.inria.fr/). It isn't
yet included in the Menhir documentation, but its section is drafted and will
be added soon.  CompCert and this repo are the only parsers written with this
backend that I'm aware of.

Jacques-Henri Jourdan, the author of the verified parser, has written a
[blog post](http://gallium.inria.fr/~scherer/gagallium/verifying-a-parser-for-a-c-compiler/index.html)
and a [journal article](http://gallium.inria.fr/~xleroy/publi/validated-parser.pdf)
describing it at a conceptual and theoretical level.

## Notes

Piecing together the OCaml bits was made harder by my lack of experience with
the languages, so there may be some dumb choices in build strategy, style,
conventions, etc. If you notice any, please let me know.

This was written as part of Joe Politz's programming languages seminar at
Swarthmore College. It's an early step in our investigation of verifying
kernel-level interpreters such as BPF.

Thanks to Jacques-Henri Jourdan, who was very open and helpful.
