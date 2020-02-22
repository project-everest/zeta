.PHONY: verify clean

# List the files that should be verified by verify-extra and verify-all
EXTRA=

# List the files that should NOT be verified at all
FLAKY=

# List the files that should be verified by verify-core and verify-all
# Those files are the roots from where all dependencies are computed
FSTAR_FILES := Veritas.SeqAux.fsti Veritas.SeqAux.fst \
               Veritas.Memory.fsti Veritas.Memory.fst \
               Veritas.BinTree.fsti Veritas.BinTree.fst \
	       Veritas.MerkleAddr.fsti Veritas.MerkleAddr.fst \
	       Veritas.Merkle.fsti Veritas.Merkle.fst \
               Veritas.SparseMerkle.fsti Veritas.SparseMerkle.fst \
	       Veritas.BinTreePtr.fsti \
               Veritas.MerkleVerifier.fst \
	       Veritas.SparseMerkleVerifier.fst

USE_EXTRACTED_INTERFACES=--use_extracted_interfaces true

OTHERFLAGS+=$(USE_EXTRACTED_INTERFACES)

# 271: theory symbols in smt patters
WARN_ERROR=--warn_error -271
SMT_OPTIONS=--z3cliopt 'timeout=600000' --z3cliopt 'smt.arith.nl=false' \
            --smtencoding.elim_box true \
            --smtencoding.l_arith_repr native \
	    --smtencoding.nl_arith_repr wrapped
OTHERFLAGS+=$(WARN_ERROR) $(SMT_OPTIONS)
ALREADY_CACHED=--already_cached 'Prims FStar'

FSTAR=fstar.exe $(OTHERFLAGS) $(ALREADY_CACHED)

# A place to put all the emitted .ml files
OUTPUT_DIRECTORY ?= _output

MY_FSTAR=$(FSTAR) --cache_checked_modules --odir $(OUTPUT_DIRECTORY)

# a.fst(i).checked is the binary, checked version of a.fst(i)
%.checked:
	$(MY_FSTAR) $<
	touch $@

all: verify

clean:
	rm -rf *.checked

.depend: $(FSTAR_FILES)
	$(MY_FSTAR) --dep full $(addprefix --include , $(INCLUDE_PATHS)) $^ > .depend

depend: .depend

include .depend

verify: $(ALL_CHECKED_FILES)

