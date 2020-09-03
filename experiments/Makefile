ifeq (,$(QD_HOME))
  $(error Please define QD_HOME)
endif

all: verify

VERITAS_SOURCES=$(filter-out ThreadState.fsti Veritas.LogStream.fsti LayeredEffect.fst,$(wildcard *.fst) $(wildcard *.fsti))

include $(HACL_HOME)/Makefile.include

FSTAR_INCLUDES=$(ALL_HACL_DIRS) $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/obj $(QD_HOME)/src/lowparse formats obj

FSTAR_OPTIONS=$(addprefix --include ,$(FSTAR_INCLUDES)) --already_cached '*,-Veritas,-LowStar.Exception,-PRFSetHash' --cache_dir obj

FSTAR_EXE=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_OPTIONS)

obj/.depend: $(VERITAS_SOURCES) Veritas.Formats.rfc
	mkdir -p formats
	$(QD_HOME)/qd -odir formats Veritas.Formats.rfc -prefix Veritas.Formats.
	mkdir -p obj
	$(FSTAR_EXE) --dep full $(VERITAS_SOURCES) $(wildcard formats/*.fst) $(wildcard formats/*.fsti) > $@

include obj/.depend

verify: $(ALL_CHECKED_FILES)

%.checked:
	mkdir -p obj
	$(FSTAR_EXE) --cache_checked_modules $<

%.fsti-in %.fst-in:
	@echo $(FSTAR_OPTIONS)

clean:
	rm -rf formats obj

.PHONY: all formats %.fsti-in %.fst-in verify clean
