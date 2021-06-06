#!/bin/bash

EVERPARSE_VERSION=v2020.12.03

everparse_basename=everparse_"$EVERPARSE_VERSION"_Linux_x86_64
everparse_tgz=$everparse_basename.tar.gz
wget https://github.com/project-everest/everparse/releases/download/$EVERPARSE_VERSION/$everparse_tgz
tar xzf $everparse_tgz
