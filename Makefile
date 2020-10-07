.PHONY: verify clean

FSTAR_HOME ?= everest/FStar
QD_HOME ?= everest/quackyducky
LOWPARSE_HOME ?= $(QD_HOME)/src/lowparse
KREMLIN_HOME ?= everest/kremlin

# List the files that should be verified by verify-extra and verify-all
EXTRA=

# List the files that should NOT be verified at all
FLAKY=

# List the files that should be verified by verify-core and verify-all
# Those files are the roots from where all dependencies are computed
FSTAR_FILES := Veritas.BinTree.fsti Veritas.BinTree.fst \
               Veritas.Key.fsti Veritas.Record.fsti \
               Veritas.SeqAux.fsti Veritas.SeqAux.fst \
               Veritas.SeqMachine.fsti Veritas.SeqMachine.fst \
               Veritas.State.fsti \
               Veritas.StateSeqMachine.fsti Veritas.StateSeqMachine.fst \
               Veritas.MultiSet.fsti Veritas.MultiSet.fst \
               Veritas.MultiSetHash.fsti Veritas.MultiSetHash.fst \
               Veritas.Hash.fsti \
               Veritas.Interleave.fsti Veritas.Interleave.fst \
               Veritas.Verifier.fst \
	       Veritas.Verifier.Thread.fsti Veritas.Verifier.Thread.fst \
               Veritas.Verifier.Global.fsti Veritas.Verifier.Global.fst \
               Veritas.EAC.fsti Veritas.EAC.fst \
               Veritas.Verifier.TSLog.fsti Veritas.Verifier.TSLog.fst \
	       Veritas.Verifier.Blum.fsti Veritas.Verifier.Blum.fst \
               Veritas.Verifier.Merkle.fsti Veritas.Verifier.Merkle.fst \
               Veritas.Verifier.EAC.fst \
               Veritas.Verifier.Correctness.fst

USE_EXTRACTED_INTERFACES=--use_extracted_interfaces true

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
ALREADY_CACHED=--already_cached 'Prims FStar LowStar'

FSTAR=fstar.exe $(OTHERFLAGS) $(ALREADY_CACHED) --cache_dir cache

# A place to put all the emitted .ml files
OUTPUT_DIRECTORY ?= _output

INCLUDE_PATHS=parsers $(OUTPUT_DIRECTORY) $(LOWPARSE_HOME) $(KREMLIN_HOME)/kremlib

FSTAR_OPTIONS=--odir $(OUTPUT_DIRECTORY) \
	      --cache_dir $(OUTPUT_DIRECTORY) \
	      $(addprefix --include , $(INCLUDE_PATHS))

MY_FSTAR=$(FSTAR) --cache_checked_modules $(FSTAR_OPTIONS)


# a.fst(i).checked is the binary, checked version of a.fst(i)
$(OUTPUT_DIRECTORY)/%.checked:
	$(MY_FSTAR) $<

all: extract

parsers: verify
	$(MAKE) -C parsers

clean:
	rm -rf *.checked .depend

.depend: $(FSTAR_FILES)
	$(MY_FSTAR) --dep full --extract 'Veritas -Veritas.SparseMerkleVerifier.Correctness' $^ > .depend

depend: .depend

include .depend

verify: $(addprefix $(OUTPUT_DIRECTORY)/,$(addsuffix .checked, $(FSTAR_FILES)))
driver: $(OUTPUT_DIRECTORY)/VeritasDriver.ml parsers VeritasDriver.fst

$(OUTPUT_DIRECTORY)/VeritasDriver.ml:
	$(MY_FSTAR) VeritasDriver.fst
	$(MY_FSTAR) --codegen OCaml VeritasDriver.fst --extract VeritasDriver

extract: verify parsers driver $(ALL_ML_FILES)
	$(MAKE) -C _output

$(OUTPUT_DIRECTORY)/%.ml:
	$(MY_FSTAR) $(subst .checked,,$(notdir $<)) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked,,$<)))


%.fst-in %.fsti.-in:
	@echo $(FSTAR_OPTIONS)
