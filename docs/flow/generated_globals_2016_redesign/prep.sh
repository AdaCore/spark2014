#!/bin/bash

for DOT in *.dot; do
    PDF=$(echo $DOT | sed -e 's/.dot/.pdf/')
    dot $DOT -Tpdf > $PDF
done
