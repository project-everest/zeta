#!/bin/bash -x
set -e # fail if any command exits with non-zero status

if [ ! -d everest ]; then
   git clone git@github.com:project-everest/everest.git
fi

cd everest

git checkout veritas

./everest pull

./everest $EVEREST_OPTS FStar make kremlin make quackyducky make MLCrypto make hacl-star make

(cd hacl-star;
 make -C dist/gcc-compatible/ install-hacl-star-raw;
 (cd bindings/ocaml && dune build && dune install))
