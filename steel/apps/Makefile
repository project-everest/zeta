# every app subdirectory makefile should set ZETA_HOME before including this
all: world

# get all the source directories
include $(ZETA_HOME)/steel/Makefile.shared

SRC_DIRS+=$(ZETA_HOME)/steel $(ZETA_HOME)/_output/cache

# other common stuff
include $(ZETA_HOME)/Makefile.common

FSTAR_FILES=$(wildcard *fst *fsti)

.PRECIOUS: %.krml
$(OUTPUT_DIRECTORY)/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen krml --cmi \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

extract: $(addprefix $(OUTPUT_DIRECTORY)/,$(STEEL_KRML_FILES)) $(filter-out $(OUTPUT_DIRECTORY)/FStar_NMST% $(OUTPUT_DIRECTORY)/FStar_MST% $(OUTPUT_DIRECTORY)/Steel_%, $(ALL_KRML_FILES))

KRML_BUNDLING_OPTIONS=-bundle 'Zeta.Steel.Application=Zeta.*,Prims,FStar.*,Hacl.*,Steel.*' \
  -library Zeta.Steel.VerifierTypes \
  -library Steel.ST.Loops \
  -library Steel.ST.Reference \
  -static-header Steel.ST.Reference \
  -no-prefix Zeta.Steel.LogEntry \
  -no-prefix Zeta.Steel.LogEntry.Spec \
  -hand-written Steel.ST.Reference

compile:
	$(KRML_HOME)/krml -warn-error +9 -skip-compilation \
          $(KRML_BUNDLING_OPTIONS) \
          $(OUTPUT_DIRECTORY)/*.krml \
          -tmpdir=$(OUTPUT_DIRECTORY)

world:
	$(MAKE) verify
	$(MAKE) extract
	$(MAKE) compile

clean:
	rm -rf $(OUTPUT_DIRECTORY) .depend

.PHONY: extract compile world all
