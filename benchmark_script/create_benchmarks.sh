#!/bin/bash

RESULTS=${PWD}/data
mkdir -p ${RESULTS}

cd ../testsuite/gnatprove
./run-tests --benchmarks --temp-dir=${RESULTS} --disable-cleanup
