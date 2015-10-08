LIB=$(FSTAR_HOME)/lib
BIN=$(FSTAR_HOME)/bin
FSTAR=$(BIN)/fstar.exe

ocaml: out hello.fst
	$(FSTAR) --odir out --codegen OCaml hello.fst
	cp $(LIB)/ml/prims.ml $(LIB)/ml/FStar_IO.ml out
	(cd out; ocamlc -o hello.exe prims.ml FStar_IO.ml Hello.ml)
	./out/hello.exe

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *~
