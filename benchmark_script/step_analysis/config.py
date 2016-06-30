#!/usr/bin/env python

TIMES = [500, 1000, 2000, 3000]
TIMES = [500, 3000]
STEPS = [1, 100, 200, 500, 5000] #, 20000]

# problematic VCs [oldflags]
# 1054f7da7554b6bb29cc058c3ad90996f40f53f4
# 57c7dbc005be1b9f19def02dd443eec357b0aef9
# 9b5302f8ee81381640d3697afdea027e82913c14

STEP_FLAGS = [
    "bitblast",
    "bv-sat-conflict",
    "cnf",
    "decision",
    "lemma",
    #"parse",
    #"preprocess",
    "quantifier",
    "restart",
    #"rewrite",
    "sat-conflict",
    "theory-check",
]
