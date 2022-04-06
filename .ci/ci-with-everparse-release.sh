#!/bin/bash

set -e
set -x

echo "TODO: publish a new EverParse release with a renamed Karamel"
false

# Set the current directory to this script's
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

[[ -d everparse ]] || ../low-level/formats/everparse/fetch_everparse.sh
export QD_HOME="$PWD/everparse"
export FSTAR_HOME="$QD_HOME"
export KREMLIN_HOME="$QD_HOME"
export PATH="$QD_HOME/bin:$PATH"

if [[ -z "$CI_THREADS" ]] ; then
    CI_THREADS=1
fi
exec make -C .. -j "$CI_THREADS" ci
