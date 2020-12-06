SRC_DIRS = high intermediate
FSTAR_FILES=$(wildcard $(addsuffix /*fst, $(SRC_DIRS))) $(wildcard $(addsuffix /*fsti, $(SRC_DIRS)))

all: verify low-level

ci: verify low-level-ci

.PHONY: ci low-level low-level-ci low-level/formats

low-level:
	+$(MAKE) -C $@

low-level-ci: low-level/formats
	+$(MAKE) -C low-level

low-level/formats:
	+$(MAKE) -C $@ regen

intermediate.verify:

include Makefile.common
