all: lowstar

DIRS=qd spec lowstar

spec: qd

steel: spec

lowstar: spec

$(DIRS): %:
	+$(MAKE) -C $@

.PHONY: $(DIRS) all
