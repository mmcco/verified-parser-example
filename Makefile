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

all:
	ocamllex Lexer.mll
	menhir --coq Parser.vy
	coqc -I validator ${VAL_FILES}
	coqc -I . -I validator Parser.v
	coqc -I . -I validator Extract.v
	ocamlc -c Specif.mli
	ocamlc -c Specif.ml
	ocamlc -c Streams.mli
	ocamlc -c Streams.ml
	ocamlc -c Parser.mli
	ocamlc -c Lexer.ml
	ocamlc -c Parser.ml
	ocamlc -c Main.mli
	ocamlc -c Main.ml
	ocamlc -I . -I validator -c run.ml
	ocamlc Lexer.cmo Parser.cmo run.cmo

clean:
	rm -f *.glob *.cmi *.cmo a.out *.vo Parser.ml Lexer.ml \
		Parser.v validator/*.vo validator/*.glob Main.ml \
		Parser.mli Lexer.mli
