# By default, build the snapshot from dist/
# This rule does not depend on EverParse
all:
	+$(MAKE) -C dist -f Makefile.basic veritasformats.a

# Regenerate the parsers into dist/ and rebuild everything
# This rule DOES depend on EverParse, but
# we run a script to automatically download the EverParse release
regen:
	+everparse/make_from_everparse_release.sh

# emacs fstar-mode stubs for this directory

FSTAR_INCLUDES=$(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/obj

FSTAR_OPTIONS=$(addprefix --include ,$(FSTAR_INCLUDES)) --already_cached '*,-Veritas.Formats'

FSTAR_EXE=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_OPTIONS)

%.fsti-in %.fst-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: all regen %.fsti-in %.fst-in
