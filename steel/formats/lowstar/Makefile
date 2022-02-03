ZETA_HOME = ../../..
include ../spec/Makefile.shared
SRC_DIRS += $(ZETA_STEEL_FORMATS_HOME)/spec $(ZETA_HOME)/_output/cache
OUTPUT_DIRECTORY ?= _output
ALREADY_CACHED_LIST='*,-Zeta.LowStar'
FSTAR_DEP_OPTIONS += --extract '*,-Steel,-FStar.NMST'
OTHERFLAGS += --cmi

KRML := $(KREMLIN_HOME)/krml
dummy := $(shell test -e $(KRML))
ifneq ($(.SHELLSTATUS),0)
  KRML := $(QD_HOME)/bin/krml
endif

all: verify

include $(ZETA_HOME)/Makefile.common

$(OUTPUT_DIRECTORY)/dist/Makefile.basic: $(ALL_KRML_FILES)
	$(KRML) -tmpdir $(dir $@) -skip-compilation \
	  $(filter %.krml,$^) \
	  -warn-error @4@5@18 \
	  -fparentheses \
	  -bundle 'Zeta.Steel.LogEntry.Spec+Zeta.LowStar.LogEntry=*[rename=ZetaFormats]' \
	  -o zetaformats.a \
	  -ccopt -Wno-type-limits

extract: $(OUTPUT_DIRECTORY)/dist/Makefile.basic

.PHONY: extract
