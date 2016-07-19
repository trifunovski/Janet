typecheck:
	ocamlc -c syntax.mli
	ocamlc -c syntax.ml
	ocamllex lexer.mll
	ocamlyacc parser.mly
	ocamlc -c parser.mli
	ocamlc -c lexer.ml
	ocamlc -c parser.ml
	rlwrap ocaml syntax.cmo lexer.cmo parser.cmo

