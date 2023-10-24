SRC_DIRS = utils generic high intermediate steel steel/crypto
FSTAR_FILES=$(wildcard $(addsuffix /*fst, $(SRC_DIRS))) $(wildcard $(addsuffix /*fsti, $(SRC_DIRS)))

all: verify

ci: extract-steel

nightly-ci: extract-all

extract-steel: verify
	+$(MAKE) -C steel
	+$(MAKE) -C steel/apps/kvstore

# This rule requires EverParse
extract-all: extract-steel
	+$(MAKE) -C steel/formats
	+$(MAKE) -C steel/apps/kvstore/everparse

.PHONY: ci extract-steel extract-all nightly-ci

include Makefile.common
