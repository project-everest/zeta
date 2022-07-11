#!/bin/bash

pushd host
oeedger8r --search-path /opt/openenclave/include --search-path /opt/openenclave/include/openenclave/edl/sgx ../openenclave_mcounter.edl --untrusted
popd
pushd enclave
oeedger8r --search-path /opt/openenclave/include --search-path /opt/openenclave/include/openenclave/edl/sgx ../openenclave_mcounter.edl --trusted
popd
