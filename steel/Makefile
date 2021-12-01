#INCLUDE_PATHS=..
#include ../Makefile.common
ZETA_HOME = ..
SRC_DIRS=$(addprefix $(ZETA_HOME)/, utils generic high intermediate steel/formats steel/crypto)
FSTAR_FILES=$(wildcard *fst *fsti)

all: verify

include ../Makefile.common

.PRECIOUS: %.krml
$(OUTPUT_DIRECTORY)/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

extract: $(filter-out $(OUTPUT_DIRECTORY)/Veritas_Intermediate% $(OUTPUT_DIRECTORY)/FStar_NMST% $(OUTPUT_DIRECTORY)/FStar_MST% $(OUTPUT_DIRECTORY)/Steel_%, $(ALL_KRML_FILES))
