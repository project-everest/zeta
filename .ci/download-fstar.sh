#!/usr/bin/env bash

# Downloads the latest F* (pre-)release

set -e
set -x

fstar_tag=$(
    if [[ -f fstar-releases.json ]]
    then
        cat fstar-releases.json
    else
        curl --silent https://api.github.com/repos/FStarLang/FStar/releases
    fi |
        jq -r 'sort_by(.created_at) | last | .tag_name'
)

[[ -n $fstar_tag ]]
fstar_version=$(echo $fstar_tag | sed 's!^v!!')
fstar_archive=fstar_"$fstar_version"_Linux_x86_64.tar.gz
[[ -f $fstar_archive ]] || curl -L -o $fstar_archive https://github.com/FStarLang/FStar/releases/download/$fstar_tag/$fstar_archive
tar xf $fstar_archive
