.PHONY: build run clean

run: TypeChecker.native
	./TypeChecker.native

clean:
	rm -f *.native

TypeChecker.native: src/*.ml
	@# -w -30: Disables warnings about different record types sharing a key name
	ocamlbuild -use-ocamlfind \
		-cflags -w,-30 \
		src/TypeChecker.native
