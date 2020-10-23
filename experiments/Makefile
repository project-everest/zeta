# JP: this Makefile does not honor OTHERFLAGS, so you can't opt out of
# verification like every other everest project

ifeq (,$(KREMLIN_HOME))
  $(error Please define KREMLIN_HOME)
endif

KRML = $(KREMLIN_HOME)/krml

KRML_OPTS = \
  -skip-compilation \
  -fnoanonymous-unions -fparentheses -fno-shadow -fcurly-braces \
  -library Veritas.Formats,Veritas.Formats.* \
  -bundle 'FStar.\*,LowStar.\*,C,C.\*[rename=Veritas_Kremlib]' \
  -bundle 'Hacl.*[rename=Veritas_Hacl]' \
  -bundle Veritas.Formats,Veritas.Formats.*[rename=Veritas_Formats] \
  -bundle Veritas.HashSet+Veritas.LowLevelVerifier+Veritas.VCache=Veritas.*[rename=Veritas] \
  $(KOPTS)

all: test-all

clean:
	rm -rf formats obj

include Makefile.include

# JP: this does not take into account changes in other directories (e.g. update
# to LowParse); consider using the technique described at
# https://fstarlang.github.io/lowstar/html/Setup.html#build
ifneq (,$(filter-out %-in,$(MAKECMDGOALS)))
obj/.depend: $(VERITAS_SOURCES) formats/Makefile
	+$(MAKE) -f Makefile.depend
endif

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
	  -o libveritascore.a -tmpdir $(dir $@)

dist/libveritascore.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

# Compiling formats

.PHONY: formats/dist/veritasformats.a

formats/dist/veritasformats.a:
	+$(MAKE) -C $(dir $@) -f Makefile.basic

# Compiling HACL*

HACL_DIST=./hacl-star/dist/gcc-compatible

hacl-star:
	@echo "Please run git submodule --init"
	false

.PHONY: $(HACL_DIST)/libevercrypt.a

$(HACL_DIST)/Makefile.config: hacl-star
	cd $(HACL_DIST) && ./configure --disable-ocaml

$(HACL_DIST)/libevercrypt.a: $(HACL_DIST)/Makefile.config
	+$(MAKE) -C $(dir $@)

# SKETCH!
#
test-all: test/mytest.c dist/libveritascore.a formats/dist/veritasformats.a $(HACL_DIST)/libevercrypt.a
	$(CC) $^

# Boilerplate

.PHONY: all %.fsti-in %.fst-in verify clean
