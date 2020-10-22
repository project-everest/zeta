# This Makefile does not build anything.
# Its goal is only to facilitate editing with emacs fstar-mode
# in this directory

all:

FSTAR_INCLUDES=$(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/obj

FSTAR_OPTIONS=$(addprefix --include ,$(FSTAR_INCLUDES)) --already_cached '*,-Veritas.Formats'

FSTAR_EXE=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_OPTIONS)

%.fsti-in %.fst-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: all %.fsti-in %.fst-in
