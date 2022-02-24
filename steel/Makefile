ZETA_HOME = ..
include Makefile.shared
FSTAR_FILES=$(wildcard *fst *fsti)

all: verify

include ../Makefile.common

.PRECIOUS: %.krml
$(OUTPUT_DIRECTORY)/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin --cmi \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

extract: $(OUTPUT_DIRECTORY)/Steel_ST_EphemeralHashtbl.krml $(OUTPUT_DIRECTORY)/Steel_ST_CancellableSpinLock.krml $(OUTPUT_DIRECTORY)/Steel_ST_SpinLock.krml $(OUTPUT_DIRECTORY)/Steel_ST_Loops.krml  $(filter-out $(OUTPUT_DIRECTORY)/FStar_NMST% $(OUTPUT_DIRECTORY)/FStar_MST% $(OUTPUT_DIRECTORY)/Steel_%, $(ALL_KRML_FILES))

compile:
	$(KREMLIN_HOME)/krml -skip-compilation $(OUTPUT_DIRECTORY)/*.krml -bundle Zeta.Steel.Main=Zeta.*,Prims,FStar.*,Hacl.*,Steel.* -library Steel.ST.SpinLock -library Steel.ST.Loops -tmpdir=$(OUTPUT_DIRECTORY)

clean:
	rm -rf $(OUTPUT_DIRECTORY)/*.krml $(OUTPUT_DIRECTORY)/*.h $(OUTPUT_DIRECTORY)/*.c $(CACHE_DIRECTORY) .depend
