.PHONY: verify clean

# List the files that should be verified by verify-extra and verify-all
EXTRA=

# List the files that should NOT be verified at all
FLAKY=

# List the files that should be verified by verify-core and verify-all
# Those files are the roots from where all dependencies are computed
FSTAR_FILES := Veritas.SeqAux.fsti Veritas.SeqAux.fst Veritas.Memory.fsti \
               Veritas.Memory.fst Veritas.Merkle.fsti Veritas.Merkle.fst \
               Veritas.MerkleVerifier.fst

USE_EXTRACTED_INTERFACES=--use_extracted_interfaces true

OTHERFLAGS+=$(USE_EXTRACTED_INTERFACES)

# 271: theory symbols in smt patters
WARN_ERROR=--warn_error -271
VALIDITY_AXIOMS?=--smtencoding.valid_intro true --smtencoding.valid_elim true
OTHERFLAGS+=$(WARN_ERROR) --z3cliopt 'timeout=600000' $(VALIDITY_AXIOMS)

FSTAR=fstar.exe $(OTHERFLAGS)

# A place to put all the emitted .ml files
OUTPUT_DIRECTORY ?= _output

MY_FSTAR=$(FSTAR) --cache_checked_modules --odir $(OUTPUT_DIRECTORY)

# a.fst.checked is the binary, checked version of a.fst
%.fst.checked: %.fst
	$(MY_FSTAR) $*.fst
	touch $@

# a.fsti.checked is the binary, checked version of a.fsti
%.fsti.checked: %.fsti
	$(MY_FSTAR) $*.fsti
	touch $@

LowStar.Printf.fst.checked: USE_EXTRACTED_INTERFACES=

verify: $(addsuffix .checked, $(FSTAR_FILES))

clean:
	rm -rf *.checked
