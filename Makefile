.PHONY: verify clean

# List the files that should be verified by verify-extra and verify-all
EXTRA=

# List the files that should NOT be verified at all
FLAKY=

SRC_DIR = high

FST_FILES := $(wildcard $(SRC_DIR)/*.fst)
FSTI_FILES := $(wildcard $(SRC_DIR)/*.fsti)
FSTAR_FILES := $(FST_FILES) $(FSTI_FILES)

INCLUDE_PATHS += high

# Uncomment the definition of PROFILE below, if you want some basic
# profiling of F* runs on Veritas files It will report the time spent
# on typechecking your file And the time spent in SMT, which is
# included in the total typechecking time

# PROFILE=--profile Veritas --profile_component 'FStar.Universal.tc_source_file FStar.SMTEncoding'

OTHERFLAGS+=$(PROFILE)

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

# a.fst.checked is the binary, checked version of a.fst
%.fst.checked: %.fst
	$(MY_FSTAR) $(addprefix --include , $(INCLUDE_PATHS)) $*.fst
	touch $@

# a.fsti.checked is the binary, checked version of a.fsti
%.fsti.checked: %.fsti
	$(MY_FSTAR) $(addprefix --include , $(INCLUDE_PATHS)) $*.fsti
	touch $@

all: verify

clean:
	rm -rf $(addsuffix .checked , $(FSTAR_FILES)) .depend

.depend: $(FSTAR_FILES)
	$(MY_FSTAR) --dep full $(addprefix --include , $(INCLUDE_PATHS)) --extract 'Veritas -Veritas.SparseMerkleVerifier.Correctness' $^ > .depend

depend: .depend

include .depend

verify: $(addsuffix .checked, $(FSTAR_FILES))

extract: $(ALL_ML_FILES)
	$(MAKE) -C _output

$(OUTPUT_DIRECTORY)/%.ml:
	$(MY_FSTAR) $(subst .checked,,$(notdir $<)) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked,,$<)))

