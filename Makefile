typecheck:
	ocamlc -c termvar.mli
	ocamlc -c termvar.ml
	ocamlc -c metavar.mli
	ocamlc -c metavar.ml
	ocamlc -c tmhshtbl.mli
	ocamlc -c tmhshtbl.ml
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
	ocamlc -c llpa1.mli
	rlwrap ocaml termvar.cmo metavar.cmo tmhshtbl.cmo syntax.cmo lexer.cmo parser.cmo typecheck.cmo llpa1.cmo

