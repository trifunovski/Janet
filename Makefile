typecheck:
	ocamlc -c syntax.mli
	ocamlc -c syntax.ml
	ocamlc -c parseterm.mli
	ocamlc -c parseterm.ml
	ocamllex lexer.mll
	ocamlyacc parser.mly
	ocamlc -c parser.mli
	ocamlc -c lexer.ml
	ocamlc -c parser.ml
	ocamlc -c typecheck.mli
	ocamlc -c typecheck.ml
	rlwrap ocaml syntax.cmo lexer.cmo parser.cmo typecheck.cmo

