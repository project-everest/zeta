ZETA_HOME = ..
include Makefile.shared
FSTAR_FILES=$(wildcard *fst *fsti)

all: verify

include ../Makefile.common

.PRECIOUS: %.krml
$(OUTPUT_DIRECTORY)/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin --cmi \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

extract: $(OUTPUT_DIRECTORY)/Steel_ST_EphemeralHashtbl.krml $(OUTPUT_DIRECTORY)/Steel_ST_CancellableSpinLock.krml $(filter-out $(OUTPUT_DIRECTORY)/FStar_NMST% $(OUTPUT_DIRECTORY)/FStar_MST% $(OUTPUT_DIRECTORY)/Steel_%, $(ALL_KRML_FILES))

compile:
	$(KREMLIN_HOME)/krml -skip-compilation $(OUTPUT_DIRECTORY)/*.krml -bundle Zeta.Steel.Main=Zeta.* -library Steel.ST.SpinLock -bundle Prims,FStar.* -tmpdir=$(OUTPUT_DIRECTORY)

clean:
	rm -rf $(OUTPUT_DIRECTORY) $(CACHE_DIRECTORY) .depend
