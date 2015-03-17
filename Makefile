VAL_FILES=validator/Alphabet.v \
	validator/Tuples.v \
	validator/Grammar.v \
	validator/Automaton.v \
	validator/Validator_safe.v \
	validator/Validator_complete.v \
	validator/Interpreter.v \
	validator/Interpreter_correct.v \
	validator/Interpreter_complete.v \
	validator/Interpreter_safe.v \
	validator/Main.v

COQ_DIRS=-I . -I validator -I includes

all:
	coqc -I validator ${VAL_FILES}
	ocamlc -c includes/Specif.mli
	ocamlc -I includes -c includes/Specif.ml
	ocamlc -c includes/Streams.mli
	ocamlc -I includes -c includes/Streams.ml
	${MAKE} incr

incr:
	ocamllex Lexer.mll
	menhir --coq Parser.vy
	coqc ${COQ_DIRS} Parser.v
	coqc ${COQ_DIRS} Datatypes.v
	coqc ${COQ_DIRS} Extract.v
	ocamlc -c Parser.mli
	ocamlfind ocamlc -package batteries -I includes -c Lexer.ml
	ocamlc -c Parser.ml
	ocamlc -c Main.mli
	ocamlc -c Main.ml
	ocamlfind ocamlc -package batteries -linkpkg \
		Parser.cmo Lexer.cmo run.ml

clean:
	rm -f *.glob *.cmi *.cmo a.out *.vo Parser.ml Lexer.ml \
		Parser.v validator/*.vo validator/*.glob Main.ml \
		Main.mli Parser.mli Lexer.mli includes/*.cmo \
		includes/*.cmi
