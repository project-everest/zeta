ZETA_HOME = ../../..
include ../spec/Makefile.shared
SRC_DIRS += $(ZETA_STEEL_FORMATS_HOME)/spec $(ZETA_HOME)/_output/cache
OUTPUT_DIRECTORY ?= _output
ALREADY_CACHED_LIST='*,-Zeta.LowStar'
FSTAR_DEP_OPTIONS += --extract '*,-Steel,-FStar.NMST,-Prims'
OTHERFLAGS += --cmi

KRML := $(KREMLIN_HOME)/krml
dummy := $(shell test -e $(KRML))
ifneq ($(.SHELLSTATUS),0)
  KRML := $(QD_HOME)/bin/krml
endif

all: verify test

include $(ZETA_HOME)/Makefile.common

dist/Makefile.basic: $(ALL_KRML_FILES)
	$(KRML) -tmpdir $(dir $@) -skip-compilation \
	  $(filter %.krml,$^) \
	  -warn-error @4@5@18 \
	  -fparentheses \
	  -bundle 'Zeta.Steel.LogEntry.Spec+Zeta.LowStar.LogEntry+Zeta.Formats.Aux.Application_key.Size+Zeta.Formats.Aux.Application_key.Low+Zeta.Formats.Aux.Application_value.Size+Zeta.Formats.Aux.Application_value.Low=*[rename=ZetaFormats]' \
	  -o zetaformats.a \
	  -add-include '"ZetaFormatsApplicationTypes.h"'
	touch $@

extract: dist/Makefile.basic

test: extract
	+$(MAKE) -C test

.PHONY: extract test
