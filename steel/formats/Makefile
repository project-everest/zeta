all: steel lowstar

DIRS=qd spec steel lowstar

spec: qd

steel: spec

lowstar: spec

$(DIRS): %:
	+$(MAKE) -C $@

.PHONY: $(DIRS) all
