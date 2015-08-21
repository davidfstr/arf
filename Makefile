.PHONY: build run clean

build: Ast.native

run: Ast.native
	./Ast.native

clean:
	rm -f Ast.native

Ast.native: src/*.ml
	@# -w -30: Disables warnings about different record types sharing a key name
	ocamlbuild -use-ocamlfind \
		-cflags -w,-30 \
		src/Ast.native
