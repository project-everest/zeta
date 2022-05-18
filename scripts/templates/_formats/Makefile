include Makefile.common

all: extract

cache/%.checked:
	$(FSTAR) $(OTHERFLAGS) $<
	@touch $@

kremlin/%.krml:
	$(FSTAR) --codegen Kremlin $(patsubst %.checked,%,$(notdir $<)) --extract_module $(basename $(patsubst %.checked,%,$(notdir $<))) --warn_error '@241'
	@touch $@

.qd_files: $(QD) $(RFC)
	$(QD) $(RFC) -low
	+$(MAKE) -f Makefile.qd_files

-include .depend

.depend: $(QD_FILES) .qd_files
	+$(MAKE) -f Makefile.depend

depend: .depend

verify: $(patsubst %,cache/%.checked,$(QD_FILES))
	echo $*

ALL_KRML_FILES := $(filter-out kremlin/prims.krml,$(ALL_KRML_FILES))

extract: $(ALL_KRML_FILES) # from .depend
	mkdir -p out
	$(KREMLIN) -warn-error '@2' -skip-compilation $^

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

clean:
	rm -rf .qd_files .depend cache kremlin out $(QD_FILES)

.PHONY: all depend verify extract clean build test
