SRC_DIRS = utils generic high intermediate steel steel/crypto
FSTAR_FILES=$(wildcard $(addsuffix /*fst, $(SRC_DIRS))) $(wildcard $(addsuffix /*fsti, $(SRC_DIRS)))

all: verify

ci: extract-steel

extract-steel: verify
	+$(MAKE) -C steel
	+$(MAKE) -C steel/formats
	+$(MAKE) -C steel/apps/kvstore

.PHONY: ci extract-steel

include Makefile.common
