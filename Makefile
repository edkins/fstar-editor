LIB=$(FSTAR_HOME)/lib
BIN=$(FSTAR_HOME)/bin
FSTAR=$(BIN)/fstar.exe

ifeq ($(OS),Windows_NT)
FSC     = fsc --mlcompatibility $(addprefix -r , $(FS_LIBS))
else
FSC     = fsharpc --mlcompatibility $(addprefix -r , $(FS_LIBS))
endif

ifeq ($(OS),Windows_NT)
FSRUNTIME =
else
FSRUNTIME = mono
endif

FS_LIBS=$(BIN)/FSharp.PowerPack.dll

LIBS=prims.fst set.fsi heap.fst st.fst all.fst io.fsti
fs: out hello.fst
	$(FSTAR) --debug hello.fst --debug_level Extreme --odir out --codegen FSharp --prims $(LIBS) hello.fst
	cp $(FS_LIBS) out
	$(FSC) -o out/hello.exe $(LIB)/fs/prims.fs $(LIB)/fs/io.fs out/Hello.fs
	$(FSRUNTIME) ./out/hello.exe

ADMITS_ML=--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi FFI --admit_fsi Runtime --admit_fsi FStar.IO
LIBS_ML=ghost.fst listTot.fst ordset.fsi ordmap.fsi classical.fst set.fsi heap.fst st.fst all.fst io.fsti

ocaml: out hello.fst
	$(FSTAR) --debug hello.fst --debug_level Extreme --odir out $(ADMITS_ML) --codegen OCaml $(LIBS_ML) hello.fst
	cp $(LIB)/ml/prims.ml $(LIB)/ml/FStar_IO.ml out
	(cd out; ocamlc -o hello.exe prims.ml FStar_IO.ml Hello.ml)
	./out/hello.exe

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *~
