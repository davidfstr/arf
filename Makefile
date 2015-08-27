.PHONY: build run clean

run: TypeCheckerTest.native
	@# OCAMLRUNPARAM=b: Print stack traces
	OCAMLRUNPARAM=b ./TypeCheckerTest.native

clean:
	rm -f *.native

TypeCheckerTest.native: src/*.ml
	@# -w -30: Disables warnings about different record types sharing a key name
	@# -g: Enable capability to print stack traces
	ocamlbuild -use-ocamlfind \
		-cflags -w,-30,-g \
		src/TypeCheckerTest.native
