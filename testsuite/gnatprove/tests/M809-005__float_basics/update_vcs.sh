#!/bin/bash

ROOT=$(pwd)

rm -rf gnatprove

cd /home/florian/projects/oxford-cde/vcs/vcs_01
git rm *
cd ..
mkdir vcs_01

cd ${ROOT}
gnatprove -P test.gpr \
    -j 4 \
    --prover smtlib2_dummy \
    -d \
    -f \
    --warnings=off \
    --report=all \
    -v \
    --proof=no_split
./clean_comments.py gnatprove/*.smt2

cp gnatprove/*.smt2 /home/florian/projects/oxford-cde/vcs/vcs_01
