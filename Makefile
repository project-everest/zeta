SRC_DIRS = high intermediate
FSTAR_FILES=$(wildcard $(addsuffix /*fst, $(SRC_DIRS))) $(wildcard $(addsuffix /*fsti, $(SRC_DIRS)))

all: verify

intermediate.verify:

include Makefile.common
