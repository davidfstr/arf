.PHONY: build test run clean deps

build: Arf.native TypeCheckerTest.native

test: TypeCheckerTest.native
	@# OCAMLRUNPARAM=b: Print stack traces
	OCAMLRUNPARAM=b ./TypeCheckerTest.native

run: Arf.native
	@# OCAMLRUNPARAM=b: Print stack traces
	OCAMLRUNPARAM=b ./Arf.native

clean:
	rm -f *.native _build

deps:
	# ocamlfind 1.5.5
	# OUnit 2.0.0
	# Batteries 2.3.1
	# core 112.35.01
	opam install \
		ocamlfind \
		ounit \
		batteries \
		core

TypeCheckerTest.native: src/*.ml
	@# -w -30: Disables warnings about different record types sharing a key name
	@# -g: Enable capability to print stack traces
	ocamlbuild -use-ocamlfind \
		-cflags -w,-30,-g \
		src/TypeCheckerTest.native

Arf.native: src/*.ml
	@# -w -30: Disables warnings about different record types sharing a key name
	@# -g: Enable capability to print stack traces
	ocamlbuild -use-ocamlfind \
		-cflags -w,-30,-g \
		src/Arf.native
