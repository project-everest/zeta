ZETA_HOME = ..
include Makefile.shared
FSTAR_FILES=$(wildcard *fst *fsti)

all:
	$(MAKE) verify
	$(MAKE) extract
	$(MAKE) compile
	$(MAKE) dist

include ../Makefile.common

.PRECIOUS: %.krml
$(OUTPUT_DIRECTORY)/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen krml --cmi \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))


#Steel files that we should extract

STEEL_KRML_FILES=Steel_ST_EphemeralHashtbl.krml \
  Steel_ST_CancellableSpinLock.krml \
  Steel_ST_SpinLock.krml \
  Steel_ST_Array_Util.krml \
  Steel_ST_Reference.krml \
  Steel_Loops.krml \
  Steel_ST_Loops.krml


extract: $(addprefix $(OUTPUT_DIRECTORY)/,$(STEEL_KRML_FILES)) $(ALL_KRML_FILES)

KRML_BUNDLING_OPTIONS=-bundle 'Zeta.Steel.SafeMain=Zeta.*,Prims,FStar.*,Hacl.*,Steel.*,EverCrypt.*,C' \
  -library Steel.ST.Loops \
  -library Steel.ST.Reference \
  -static-header Steel.ST.Reference \
  -header noheader.txt \
  -no-prefix Zeta.Steel.LogEntry \
  -no-prefix Zeta.Steel.LogEntry.Spec \
  -hand-written Steel.ST.Reference

KRML_ATOMIC_CAS_INCLUDE_OPTION=-add-include \"steel_atomics.h\"
KRML_APP_INCLUDE_OPTION=-add-include \"zeta_application.h\"

compile:
	$(KRML_HOME)/krml -warn-error +9 -skip-compilation \
		$(KRML_BUNDLING_OPTIONS) \
		$(OUTPUT_DIRECTORY)/*.krml \
		-tmpdir=$(OUTPUT_DIRECTORY) \
		$(KRML_ATOMIC_CAS_INCLUDE_OPTION) \
		$(KRML_APP_INCLUDE_OPTION)

dist:
	cp $(OUTPUT_DIRECTORY)/*.c $(DIST_DIRECTORY)/
	cp $(OUTPUT_DIRECTORY)/*.h $(DIST_DIRECTORY)/
	if test -d $(OUTPUT_DIRECTORY)/internal ; then cp -r $(OUTPUT_DIRECTORY)/internal $(DIST_DIRECTORY)/ ; fi
	cp -r $(KRML_HOME)/include/* $(DIST_DIRECTORY)/
	cp -r $(KRML_HOME)/krmllib/dist/minimal/*.h $(DIST_DIRECTORY)/

clean_c:
	rm -rf $(OUTPUT_DIRECTORY)/*.h $(OUTPUT_DIRECTORY)/*.c

clean: clean_c
	rm -rf $(OUTPUT_DIRECTORY)/*.krml $(CACHE_DIRECTORY) .depend

CORE_STEEL_MODULES=EpochMap ExternalPtr HashAccumulator HashValue Main SafeMain \
		   SafeMain.Handle Util Verifier VerifierSteps VerifierTypes AggregateEpochHashes \
                   Application ApplicationRecord ApplicationResult ApplicationTypes \
                   BitUtils EpochHashes Globals Log LogEntry.Spec LogEntry.Types LogEntry \
		   Parser
GHOST_STATE_MODULES=ThreadLogMap
SPEC_MODULES=ThreadStateModel MultiSetHash
SIMULATION_MODULES=AddMRel AppSim GlobalRel KeyUtils LogRel Rel RelHashFunction \
		   StoreRel Thread ThreadRel ThreadRelDef ThreadSim

wc:
	echo "CORE STEEL"
	wc -l $(addprefix Zeta.Steel., $(addsuffix .fst*, $(CORE_STEEL_MODULES)))

	echo "SPEC"
	wc -l $(addprefix Zeta.Steel., $(addsuffix .fst*, $(SPEC_MODULES)))

	echo "GHOST STATE"
	wc -l $(addprefix Zeta.Steel., $(addsuffix .fst*, $(GHOST_STATE_MODULES))) $(FSTAR_HOME)/ulib/experimental/Steel.FractionalAnchoredPreorder.fst*

	echo "SIMULATION"
	wc -l Zeta.Correctness.fst* $(addprefix Zeta.Steel., $(addsuffix .fst*, $(SIMULATION_MODULES)))



.PHONY: extract compile dist clean_c wc
