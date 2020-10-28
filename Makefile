INCLUDE_PATHS=parsers
include Makefile.common

all: verify

parsers: verify
	$(MAKE) -C parsers

clean:
	rm -rf *.checked .depend

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
