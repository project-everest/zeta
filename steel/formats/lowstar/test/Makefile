all: test

OUT_FILES=Makefile.basic Makefile.include
DIST_FILES=ZetaFormats.c ZetaFormats.h

$(OUT_FILES): %: ../out/%
	cp $^ $@

$(DIST_FILES): %: ../../../dist/%
	cp $^ $@

test: $(OUT_FILES) $(DIST_FILES)
	+$(MAKE) -f Makefile.basic USER_CFLAGS='-Wno-type-limits'

clean:
	+$(MAKE) -f Makefile.basic clean || true
	rm -f $(FILES)

.PHONY: all test clean
