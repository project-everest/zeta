SRC_DIRS = utils generic high intermediate steel steel/crypto
FSTAR_FILES=$(wildcard $(addsuffix /*fst, $(SRC_DIRS))) $(wildcard $(addsuffix /*fsti, $(SRC_DIRS)))

all: verify

ci: steel/formats

steel/formats: verify
	+$(MAKE) -C $@

.PHONY: ci low-level low-level-ci low-level/formats steel/formats

low-level:
	+$(MAKE) -C $@

low-level-ci: low-level/formats
	+$(MAKE) -C low-level

low-level/formats:
	cp $@/Veritas.Formats.Types.fst types.old
	+$(MAKE) -C $@ regen
	diff types.old $@/Veritas.Formats.Types.fst
	rm -f types.old

intermediate.verify:

include Makefile.common
