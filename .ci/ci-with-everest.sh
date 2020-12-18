#!/bin/bash

set -e
set -x

# Set the current directory to this script's
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

if [[ -z "$CI_THREADS" ]] ; then
    CI_THREADS=1
fi

EVEREST_OPTS="--yes" ../everest-deps.sh check
export PATH="$PWD/everest/z3/bin:$PATH"
EVEREST_OPTS="--yes -j $CI_THREADS --admit" ../everest-deps.sh build
source ../everest-deps.sh setenv

exec make -C .. -j "$CI_THREADS" ci
