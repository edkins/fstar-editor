LIB=$(FSTAR_HOME)/lib
BIN=$(FSTAR_HOME)/bin
FSTAR=$(BIN)/fstar.exe

ADMIT=--admit_fsi FStar.Set --admit_fsi FStar.Heap --admit_fsi FStar.ST --admit_fsi FStar.All --admit_fsi FStar.IO
LIBFILES=set.fsi heap.fst st.fst all.fst io.fsti string.fst list.fst char.fst

ocaml: out hello.fst
	$(FSTAR) --odir out --codegen OCaml $(ADMIT) $(LIBFILES) terminal.fst hello.fst
	cp $(LIB)/ml/prims.ml $(LIB)/ml/FStar_IO.ml $(LIB)/ml/FStar_ST.ml $(LIB)/ml/FStar_String.ml $(LIB)/ml/FStar_List.ml out
	(cd out; ocamlfind ocamlc -o hello.exe -package batteries -linkpkg prims.ml FStar_IO.ml FStar_ST.ml FStar_List.ml FStar_String.ml Hello.ml)
	stty -echo -icanon
	./out/hello.exe
	stty echo icanon

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *~
