#!/bin/bash

JOBS=$(cat /proc/cpuinfo | grep processor | wc -l)

RESULTS=${PWD}/data
mkdir -p ${RESULTS}

cd ../testsuite/gnatprove
./run-tests --debug --benchmarks -j${JOBS} \
            --temp-dir=${RESULTS} --disable-cleanup
