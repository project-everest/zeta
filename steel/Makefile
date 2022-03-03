ZETA_HOME = ..
include Makefile.shared
FSTAR_FILES=$(wildcard *fst *fsti)

all: verify

include ../Makefile.common

.PRECIOUS: %.krml
$(OUTPUT_DIRECTORY)/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin --cmi \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))


#Steel files that we should extract

STEEL_KRML_FILES=Steel_ST_EphemeralHashtbl.krml \
  Steel_ST_CancellableSpinLock.krml \
  Steel_ST_SpinLock.krml \
  Steel_ST_Array_Util.krml \
  Steel_ST_Reference.krml \
  Steel_ST_Loops.krml


extract: $(addprefix $(OUTPUT_DIRECTORY)/,$(STEEL_KRML_FILES)) $(filter-out $(OUTPUT_DIRECTORY)/FStar_NMST% $(OUTPUT_DIRECTORY)/FStar_MST% $(OUTPUT_DIRECTORY)/Steel_%, $(ALL_KRML_FILES))

KRML_BUNDLING_OPTIONS=-bundle Zeta.Steel.Main=Zeta.*,Prims,FStar.*,Hacl.*,Steel.* \
  -library Steel.ST.Loops \
  -library Steel.ST.Reference \
  -static-header Steel.ST.Reference \
  -hand-written Steel.ST.Reference

compile:
	$(KREMLIN_HOME)/krml -skip-compilation $(KRML_BUNDLING_OPTIONS) $(OUTPUT_DIRECTORY)/*.krml -tmpdir=$(OUTPUT_DIRECTORY)

clean:
	rm -rf $(OUTPUT_DIRECTORY)/*.krml $(OUTPUT_DIRECTORY)/*.h $(OUTPUT_DIRECTORY)/*.c $(CACHE_DIRECTORY) .depend
