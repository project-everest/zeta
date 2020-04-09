TARGET=Veritas_Driver.native

$(TARGET):
	rm -f $@
	OCAMLPATH="$(FSTAR_HOME)/bin" ocamlbuild -use-menhir -tag thread -use-ocamlfind -quiet -pkg batteries -pkg fstarlib -cflags -w,-8 $@

clean:
	rm -rf _build $(TARGET)
