ZETA_HOME = ../../..
ZETA_STEEL_HOME=$(ZETA_HOME)/steel
ZETA_STEEL_FORMATS_HOME=$(ZETA_STEEL_HOME)/formats
include $(ZETA_STEEL_FORMATS_HOME)/Makefile.shared
SRC_DIRS += $(ZETA_STEEL_FORMATS_HOME)/aux $(ZETA_STEEL_FORMATS_HOME)/aux/obj
FSTAR_FILES=$(wildcard *.fst *.fsti)
ALREADY_CACHED_LIST='*,-Zeta.Steel.ApplicationRecord,-Zeta.Formats,+Zeta.Formats.Aux,-Zeta.Formats.Aux.External,-Zeta.Formats.Aux.Significant_digits_t,-Zeta.Formats.Aux.Application_key,-Zeta.Formats.Aux.Application_value,-Zeta.Formats.Aux.Internal_key'

all: verify

include $(ZETA_HOME)/Makefile.common
