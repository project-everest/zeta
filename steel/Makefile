ZETA_HOME = ..
include Makefile.shared
FSTAR_FILES=$(wildcard *fst *fsti)

all:
	$(MAKE) verify
	$(MAKE) extract
	$(MAKE) compile
	$(MAKE) dist

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

KRML_BUNDLING_OPTIONS=-bundle 'Zeta.Steel.Main=Zeta.*,Prims,FStar.*,Hacl.*,Steel.*' \
  -library Steel.ST.Loops \
  -library Steel.ST.Reference \
  -static-header Steel.ST.Reference \
  -no-prefix Zeta.Steel.LogEntry \
  -no-prefix Zeta.Steel.LogEntry.Spec \
  -hand-written Steel.ST.Reference

KRML_ATOMIC_CAS_INCLUDE_OPTION=-add-include \"steel_atomics.h\"
KRML_APP_INCLUDE_OPTION=-add-include \"zeta_application.h\"

compile:
	$(KREMLIN_HOME)/krml -warn-error +9 -skip-compilation \
		$(KRML_BUNDLING_OPTIONS) \
		$(OUTPUT_DIRECTORY)/*.krml \
		-tmpdir=$(OUTPUT_DIRECTORY) \
		$(KRML_ATOMIC_CAS_INCLUDE_OPTION) \
		$(KRML_APP_INCLUDE_OPTION)

dist: $(OUTPUT_DIRECTORY)/*.c $(OUTPUT_DIRECTORY)/*.h
	cp $(OUTPUT_DIRECTORY)/*.c $(DIST_DIRECTORY)/
	cp $(OUTPUT_DIRECTORY)/*.h $(DIST_DIRECTORY)/

clean_c:
	rm -rf $(OUTPUT_DIRECTORY)/*.h $(OUTPUT_DIRECTORY)/*.c

clean: clean_c
	rm -rf $(OUTPUT_DIRECTORY)/*.krml $(CACHE_DIRECTORY) .depend
