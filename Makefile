LIB=$(FSTAR_HOME)/lib
BIN=$(FSTAR_HOME)/bin
FSTAR=$(BIN)/fstar.exe

ocaml: out hello.fst
	$(FSTAR) --odir out --codegen OCaml hello.fst
	cp $(LIB)/ml/prims.ml $(LIB)/ml/FStar_IO.ml $(LIB)/ml/FStar_ST.ml out
	(cd out; ocamlc -o hello.exe prims.ml FStar_IO.ml FStar_ST.ml Hello.ml)
	stty -echo -icanon
	./out/hello.exe
	stty echo icanon

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *~
