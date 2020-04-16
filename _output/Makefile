TARGET=VeritasDriver.native

ifeq ($(OS),Windows_NT)
  export OCAMLPATH := $(FSTAR_HOME)/bin;$(OCAMLPATH)
else
  export OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)
endif


$(TARGET):
	rm -f $@
	OCAMLPATH="$(FSTAR_HOME)/bin" ocamlbuild -use-menhir -tag thread -use-ocamlfind -quiet -pkg batteries -pkg fstarlib -pkg hacl-star -cflags -w,-8 $@

clean:
	git clean -fdx .
