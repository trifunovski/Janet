#
# Pure OCaml, package from Opam, two directories
#

# - The -I flag introduces sub-directories
# - -use-ocamlfind is required to find packages (from Opam)
# - _tags file introduces packages, bin_annot flag for tool chain
# - using *.mll and *.mly are handled automatically

# - we are using menhir, the modern replacement for OCamlYacc
# OCB_FLAGS = -use-ocamlfind             -I src -I lib # uses ocamlyacc
OCB_FLAGS   = -no-ocamlfind -I main -I vars -I lexandparse -I backbone -I sets -I tables -I tpcheck # uses menhir

OCB = 		ocamlbuild $(OCB_FLAGS)

all: 		native byte # profile debug

clean:
			$(OCB) -clean

native:
			$(OCB) llpa1.native

byte:
			$(OCB) llpa1.byte

profile:
			$(OCB) -tag profile llpa1.native

debug:
			$(OCB) -tag debug llpa1.byte

test: 		native
			./llpa1.run ()

.PHONY: 	all clean byte native profile debug sanity test
