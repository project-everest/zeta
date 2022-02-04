all: steel lowstar

DIRS=aux spec steel lowstar

spec: aux

steel: spec

lowstar: spec

$(DIRS): %:
	+$(MAKE) -C $@

.PHONY: $(DIRS) all
