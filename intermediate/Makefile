#INCLUDE_PATHS=..
#include ../Makefile.common
VERITAS_HOME = ..
SRC_DIRS = . ../high
FSTAR_FILES=$(wildcard *fst *fsti)

all: verify

Veritas.Intermediate.Verify.fst-in: OTHERFLAGS+=--z3rlimit_factor 4

$(CACHE_DIRECTORY)/Veritas.Intermediate.Verify.fst.checked: OTHERFLAGS+=--z3rlimit_factor 4

include ../Makefile.common
