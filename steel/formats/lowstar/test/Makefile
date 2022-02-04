all: test

FILES=Makefile.basic Makefile.include ZetaFormats.c ZetaFormats.h

$(FILES): %: ../dist/%
	cp $^ $@

test: $(FILES)
	+$(MAKE) -f Makefile.basic USER_CFLAGS='-Wno-type-limits'

clean:
	+$(MAKE) -f Makefile.basic clean || true
	rm -f $(FILES)

.PHONY: all test clean
