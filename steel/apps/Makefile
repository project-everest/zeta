# every app subdirectory makefile should set ZETA_HOME before including this

# get all the source directories
include $(ZETA_HOME)/steel/Makefile.shared

SRC_DIRS+=$(ZETA_HOME)/steel

# other common stuff
include $(ZETA_HOME)/Makefile.common

all:
	$(MAKE) verify
