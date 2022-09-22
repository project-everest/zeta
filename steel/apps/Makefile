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

STEEL_KRML_FILES=Steel_ST_EphemeralHashtbl.krml \
  Steel_ST_CancellableSpinLock.krml \
  Steel_ST_SpinLock.krml \
  Steel_ST_Array_Util.krml \
  Steel_ST_Reference.krml \
  Steel_Loops.krml \
  Steel_ST_Loops.krml

extract: $(addprefix $(OUTPUT_DIRECTORY)/,$(STEEL_KRML_FILES)) $(filter-out $(OUTPUT_DIRECTORY)/FStar_NMST% $(OUTPUT_DIRECTORY)/FStar_MST% $(OUTPUT_DIRECTORY)/Steel_%, $(ALL_KRML_FILES))

KRML_BUNDLE_ROOT ?= Zeta.Steel.Application

KRML_BUNDLING_OPTIONS += -bundle $(KRML_BUNDLE_ROOT)'=Zeta.*,Prims,FStar.*,Hacl.*,Steel.*,LowStar.*,C.*,LowParse.*' \
  -library Steel.ST.Loops \
  -library Steel.ST.Reference \
  -static-header Steel.ST.Reference \
  -no-prefix Zeta.Steel.LogEntry \
  -no-prefix Zeta.Steel.LogEntry.Spec \
  -header $(ZETA_HOME)/steel/noheader.txt \
  -hand-written Steel.ST.Reference

compile:
	$(KRML_HOME)/krml -warn-error +9 -skip-compilation \
          $(KRML_BUNDLING_OPTIONS) \
          $(OUTPUT_DIRECTORY)/*.krml \
          -tmpdir=$(OUTPUT_DIRECTORY)

dist:
	mkdir -p $(APP_DIST_DIRECTORY)
	cp $(OUTPUT_DIRECTORY)/*.h $(APP_DIST_DIRECTORY) 
	cp $(OUTPUT_DIRECTORY)/*.c $(APP_DIST_DIRECTORY) 

world:
	$(MAKE) verify
	$(MAKE) extract
	$(MAKE) compile
	$(MAKE) dist

clean:
	rm -rf $(OUTPUT_DIRECTORY) .depend

.PHONY: extract compile world all dist
