ifeq (,$(FSTAR_HOME))
  $(error Please define FSTAR_HOME)
endif

ifeq (,$(KREMLIN_HOME))
  $(error Please define KREMLIN_HOME)
endif

KRML := $(KREMLIN_HOME)/krml
dummy := $(shell test -e $(KRML))
ifneq ($(.SHELLSTATUS),0)
  KRML := $(QD_HOME)/bin/krml
endif

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

# From https://fstarlang.github.io/lowstar/html/Setup.html#build
ifndef MAKE_RESTARTS
obj/.depend: .FORCE
	+$(MAKE) -f Makefile.depend
.PHONY: .FORCE
.FORCE:
endif

include obj/.depend

verify: $(ALL_CHECKED_FILES)

%.checked:
	$(FSTAR_EXE) --cache_checked_modules $<
	touch $@

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
	$(CC) $^ -o mytest && ./mytest

# Boilerplate

.PHONY: all %.fsti-in %.fst-in verify clean
