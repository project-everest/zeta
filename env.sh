#!/bin/bash
PWD=`pwd`

is_windows () {
  [[ $OS == "Windows_NT" ]]
}

if is_windows; then
    export EVEREST_HOME=`cygpath -m $PWD/everest`
    export FSTAR_HOME=`cygpath -m $EVEREST_HOME/FStar`
    export KREMLIN_HOME=`cygpath -m $EVEREST_HOME/kremlin`
    export VALE_HOME=`cygpath -m $EVEREST_HOME/vale`
    export QD_HOME=`cygpath -m $EVEREST_HOME/quackyducky`
    export EVERPARSE_HOME=`cygpath -m $EVEREST_HOME/quackyducky`
    export MLCRYPTO_HOME=`cygpath -m $EVEREST_HOME/MLCrypto`
    export PATH=`cygpath -u $EVEREST_HOME/z3/bin`:`cygpath -u $FSTAR_HOME/bin`:`cygpath -u $QD_HOME`:$PATH
else
    export EVEREST_HOME=$PWD/everest
    export FSTAR_HOME=$EVEREST_HOME/FStar
    export KREMLIN_HOME=$EVEREST_HOME/kremlin
    export VALE_HOME=$EVEREST_HOME/vale
    export QD_HOME=$EVEREST_HOME/quackyducky
    export EVERPARSE_HOME=$EVEREST_HOME/quackyducky
    export MLCRYPTO_HOME=$EVEREST_HOME/MLCrypto
    export PATH=$EVEREST_HOME/z3/bin:$FSTAR_HOME/bin:$QD_HOME:$PATH
fi


