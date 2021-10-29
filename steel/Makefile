#INCLUDE_PATHS=..
#include ../Makefile.common
VERITAS_HOME = ..
SRC_DIRS=$(VERITAS_HOME)/high $(VERITAS_HOME)/intermediate $(VERITAS_HOME)/steel/formats $(VERITAS_HOME)/steel/crypto $(VERITAS_HOME)/utils
FSTAR_FILES=$(wildcard *fst *fsti)

all: verify

include ../Makefile.common

.PRECIOUS: %.krml
$(OUTPUT_DIRECTORY)/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

extract: $(filter-out $(OUTPUT_DIRECTORY)/Veritas_Intermediate% $(OUTPUT_DIRECTORY)/FStar_NMST% $(OUTPUT_DIRECTORY)/FStar_MST% $(OUTPUT_DIRECTORY)/Steel_%, $(ALL_KRML_FILES))
