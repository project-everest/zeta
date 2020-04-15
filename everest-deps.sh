#!/bin/bash

is_windows () {
  [[ $OS == "Windows_NT" ]]
}

set -x # echo commands
set -e # fail if any command exits with non-zero status

git clone git@github.com:project-everest/everest.git
git checkout veritas

PWD=`pwd`
if is_windows;
   export EVEREST_HOME=`cygpath -m $PWD/everest`
   export FSTAR_HOME=`cygpath -m $PWD/everest/FStar`
   export KREMLIN_HOME=`cygpath -m $PWD/everest/kremlin`
   export VALE_HOME=`cygpath -m $PWD/everest/vale`
   export QD_HOME=`cygpath -m $PWD/everest/quackyducky`
   export EVERPARSE_HOME=`cygpath -m $PWD/everest/quackyducky`
   export MLCRYPTO_HOME=`cygpath -m $PWD/everest/MLCrypto`
   export PATH=`cygpath -u $EVEREST_HOME/z3/bin`:`cygpath -u $FSTAR_HOME/bin`:`cygpath -u $QD_HOME`:$PATH
else
   export EVEREST_HOME=$PWD/everest
   export FSTAR_HOME=$PWD/everest/FStar
   export KREMLIN_HOME=$PWD/everest/kremlin
   export VALE_HOME=$PWD/everest/vale
   export QD_HOME=$PWD/everest/quackyducky
   export EVERPARSE_HOME=$PWD/everest/quackyducky
   export MLCRYPTO_HOME=$PWD/everest/MLCrypto
   export PATH=$EVEREST_HOME/z3/bin:$FSTAR_HOME/bin:$QD_HOME:$PATH
fi

cd everest

./everest pull

./everest $EVEREST_OPTS FStar make kremlin make quackyducky make hacl-star make

(cd hacl-star;
 make -C dist/gcc-compatible/ install-hacl-raw;
 (cd bindings/ocaml && dune install))
