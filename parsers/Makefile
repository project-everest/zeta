include Makefile.common

all: verify extract-ocaml

cache/%.checked:
	$(FSTAR) $(OTHERFLAGS) $<
	@touch $@

extracted/%.ml:
	$(FSTAR) --codegen OCaml $(patsubst %.checked,%,$(notdir $<)) --extract_module $(basename $(patsubst %.checked,%,$(notdir $<))) --warn_error '@241'
	@touch $@

extracted/%.krml:
	$(FSTAR) --codegen Kremlin $(patsubst %.checked,%,$(notdir $<)) --extract_module $(basename $(patsubst %.checked,%,$(notdir $<))) --warn_error '@241'
	@touch $@

extracted/%.cmx:
	ocamlopt -c -I $(FSTAR_HOME)/bin/fstarlib -I $(KREMLIN_HOME)/_build/kremlib -I extracted $<

.qd_files: $(QD) $(RFC)
	$(QD) -high -prefix VeritasFormats. $(RFC)
	+$(MAKE) -f Makefile.qd_files

-include .depend

.depend: $(QD_FILES) .qd_files
	+$(MAKE) -f Makefile.depend

depend: .depend

verify: $(patsubst %,cache/%.checked,$(QD_FILES))
	echo $*

ALL_KRML_FILES := $(filter-out extracted/prims.krml,$(ALL_KRML_FILES))

ALL_CMX_FILES=$(patsubst %.ml,%.cmx,$(ALL_ML_FILES))

extract-ocaml: $(ALL_CMX_FILES)

extract-kremlin: $(ALL_KRML_FILES) # from .depend
	mkdir -p out
	$(KREMLIN) -warn-error '@2' -skip-compilation $^

# test.exe: $(ALL_KRML_FILES)
# 	mkdir -p out
# 	$(KREMLIN) $(LOWPARSE_HOME)/LowParse_TestLib_Low_c.c -no-prefix Test $^ -o test.exe

# test: test.exe
# 	./test.exe

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

clean:
	rm -rf .qd_files .depend cache extracted ocaml out $(filter-out VeritasFormats.fst VeritasFormats.fsti VeritasFormats.Addr.fst VeritasFormats.Merkle_addr.fst VeritasFormats.Hash_value.fst,$(QD_FILES)) test.exe

.PHONY: all depend verify extract-ocaml extract-kremlin clean build test
