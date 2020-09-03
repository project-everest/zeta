ifeq (,$(QD_HOME))
  $(error Please define QD_HOME)
endif

all: verify

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
	test -f obj/.depend
	+$(MAKE) $(ALL_CHECKED_FILES)

%.checked:
	mkdir -p obj
	$(FSTAR_EXE) --cache_checked_modules $<

%.fsti-in %.fst-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: all %.fsti-in %.fst-in verify clean
