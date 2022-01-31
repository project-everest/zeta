all: steel

DIRS=aux spec steel

spec: aux

steel: spec

$(DIRS): %:
	+$(MAKE) -C $@

.PHONY: $(DIRS) all
