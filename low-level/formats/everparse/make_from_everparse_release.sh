#!/bin/bash

set -e
set -x

EVERPARSE_VERSION=v2020.12.03

# Set the current directory to this script's
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

if [[ -z "$QD_HOME" ]] ; then
    # QD_HOME does not point to EverParse.
    if ! [[ -d everparse ]] ; then
        # EverParse is not here. Pull the binary package.
        ./fetch_everparse.sh
        # Reuse extracted *.krml from the binary package
        mkdir -p obj
        cp -p everparse/src/3d/prelude/*.krml obj/
    fi
    export QD_HOME=$PWD/everparse
    # Override F* and KReMLin with the ones from the binary package
    # because that package contains .checked files that
    # only work with the F* and KReMLin binaries included in that package
    export FSTAR_HOME=$QD_HOME
    export KREMLIN_HOME=$QD_HOME
    # add the package binary directory to the PATH to locate z3
    export PATH=$QD_HOME/bin:$PATH
fi

exec make "$@"
