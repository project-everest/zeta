all: spec

DIRS=aux spec

spec: aux

$(DIRS): %:
	+$(MAKE) -C $@

.PHONY: $(DIRS) all
