a.out:
	ocamlc -c eval.mli
	menhir parser.mly
	ocamllex lexer.mll
	ocamlc eval.ml parser.mli parser.ml lexer.ml print.ml

.PHONY: clean
clean:
	rm -f parser.ml parser.mli lexer.ml *.cmi *.cmx *.cmo *.o *~ a.out
