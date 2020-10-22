# JP: this Makefile does not honor OTHERFLAGS, so you can't opt out of
# verification like every other everest project

ifeq (,$(QD_HOME))
  $(error Please define QD_HOME)
endif

ifeq (,$(KREMLIN_HOME))
  $(error Please define KREMLIN_HOME)
endif

KRML = $(KREMLIN_HOME)/krml

KRML_OPTS = \
  -skip-compilation \
  -fnoanonymous-unions -fparentheses -fno-shadow -fcurly-braces \
  -library EverCrypt,EverCrypt.*,Hacl.* \
  -bundle 'EverCrypt,EverCrypt.\*[rename=EverCrypt]' \
  -bundle 'LowParse.\*,LowParseWrappers[rename=LowParse]' \
  -bundle 'FStar.\*,LowStar.\*,C,C.\*[rename=Veritas_Kremlib]' \
  -bundle 'Spec.\*' \
  -bundle 'Test.\*' \
  -bundle 'Meta.\*' \
  -bundle 'Lib.*[rename=Hacl_Lib]' \
  -bundle 'Vale.*,Hacl.*[rename=ShouldBeUnused1]' \
  -bundle Veritas.Formats+Veritas.HashSet+Veritas.LowLevelVerifier+Veritas.Reveal+Veritas.VCache=[rename=Veritas] \
  $(KOPTS)

all: verify dist/Makefile.basic

clean:
	rm -rf formats obj

include Makefile.include

formats/Makefile: Makefile.formats Veritas.Formats.rfc
	mkdir -p formats
	$(QD_HOME)/qd -odir formats Veritas.Formats.rfc -prefix Veritas.Formats.
	cp $< $@

obj/.depend: $(VERITAS_SOURCES) formats/Makefile
	+$(MAKE) -f Makefile.depend

-include obj/.depend

verify:
	@# JP: because of the current architecture using a recursive make, this
	@# will produce every checked file twice: once for the verify target in
	@# the sub-make, and one for the parent make (via krml files) which is
	@# unaware that the sub-make is producing the required checked files too
	test -f obj/.depend
	+$(MAKE) $(ALL_CHECKED_FILES)

%.checked:
	@# JP: I think we've had races on CI in the past where two processes
	@# concurrently try to create the same directory
	mkdir -p obj
	@# JP: this is missing the "touch $@" which results in spurious rebuilds, e.g. 
	@#      Prerequisite `obj/Veritas.Formats.Vlog_entry.fsti.checked' is newer than target `obj/Veritas.Formats.fst.checked'.
	@#      Must remake target `obj/Veritas.Formats.fst.checked'.
	@# Use make --debug to debug those.
	$(FSTAR_EXE) --cache_checked_modules $< --admit_smt_queries true

%.fsti-in %.fst-in:
	@echo $(FSTAR_OPTIONS)

obj/%.krml:
	$(FSTAR_EXE) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

dist/Makefile.basic: $(ALL_KRML_FILES)
	mkdir -p $(dir $@)
	$(KRML) $(KRML_OPTS) $^ \
	  -o libveritas.so -tmpdir $(dir $@)

.PHONY: all %.fsti-in %.fst-in verify clean
