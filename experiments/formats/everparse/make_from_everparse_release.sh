#!/bin/bash

set -e
set -x

EVERPARSE_VERSION=v2020.10.23

# Set the current directory to this script's
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

if [[ -z "$QD_HOME" ]] ; then
    # QD_HOME does not point to EverParse.
    if ! [[ -d everparse ]] ; then
        # EverParse is not here. Pull the binary package.
        everparse_basename=everparse_"$EVERPARSE_VERSION"_Linux_x86_64
        everparse_tgz=$everparse_basename.tar.gz
        wget https://github.com/project-everest/everparse/releases/download/$EVERPARSE_VERSION/$everparse_tgz
        tar xzf $everparse_tgz
    fi
    export QD_HOME=$PWD/everparse
    # Override F* and KReMLin with the ones from the binary package
    # because that package contains .checked files that
    # only work with the F* and KReMLin binaries included in that package
    export FSTAR_HOME=$QD_HOME
    export KREMLIN_HOME=$QD_HOME
fi

exec make "$@"
