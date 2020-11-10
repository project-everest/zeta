#!/bin/bash
set -e # fail if any command exits with non-zero status

print_usage () {
  cat <<HELP

$0, a wrapper around everest scripts to install what's needed for
Veritas. It clones the everest repositories in the current folder.

You can pass options to the everest script by setting the
EVEREST_OPTS variable.

A typical usage is:

1. Run "everest-deps.sh check" to install all external dependences of everest,
   e.g., ocaml, opam etc. You should need to do this step only once.

2. Run "EVEREST_OPTS='-j 8' everest-deps.sh build", to build
   everything that's needed, notably F*, Kremlin, EverParse and HACL*,
   including ocaml bindings for EverCrypt installed as the opam
   package hacl-star.

   You might run this step occasionally, in case you want to take
   updates from F* etc. You might also include the "--admit" in
   EVEREST_OPTS to admit SMT proof obligations in the everest
   projects, to make it complete a bit faster (though you wouldn't do
   this if you really wanted to prove everything, e.g.,

   "EVEREST_OPTS='-j 8 --admit' everest-deps.sh build"

3. Run "source everest-deps.sh setenv" to export environment variables
   to use the version of F*, Kremlin, etc. that were built in step 2.

HELP
}

do_clone () {

    if [ ! -d everest ]; then
        git clone git@github.com:project-everest/everest.git
    fi

    (cd everest; git checkout veritas)
}

do_build () {
    do_clone

    cd everest

    ./everest pull

    ./everest $EVEREST_OPTS FStar make kremlin make quackyducky make MLCrypto make hacl-star make

    (cd hacl-star;
     make -C dist/gcc-compatible/ install-hacl-star-raw;
     (cd bindings/ocaml &&
          dune build &&
          dune install &&
          dune runtest))
}

do_check () {
    do_clone

    cd everest

    ./everest check
}

is_windows () {
  [[ $OS == "Windows_NT" ]]
}

do_setenv() {
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
}

case "$1" in
    check)
        do_check
        ;;

    build)
        do_build
        ;;

    setenv)
        do_setenv
        ;;

    *)
        print_usage
        ;;
esac
