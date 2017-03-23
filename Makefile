typecheck:
	ocamlc -c termvar.mli
	ocamlc -c termvar.ml
	ocamlc -c metavar.mli
	ocamlc -c metavar.ml
	ocamlc -c placevar.mli
	ocamlc -c placevar.ml
	ocamlc -c tmhshtbl.mli
	ocamlc -c tmhshtbl.ml
	ocamlc -c plhshtbl.mli
	ocamlc -c plhshtbl.ml
	ocamlc -c tmvarrest.mli
	ocamlc -c tmvarrest.ml
	ocamlc -c placerest.mli
	ocamlc -c placerest.ml
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
	rlwrap ocaml termvar.cmo metavar.cmo placevar.cmo tmhshtbl.cmo plhshtbl.cmo syntax.cmo tmvarrest.cmo placerest.cmo lexer.cmo parser.cmo typecheck.cmo

