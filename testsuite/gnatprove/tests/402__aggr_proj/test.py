from test_support import DirectorySeparatorRefiner, default_refiners, prove_all

# The message about the created object directory contains a relative path, so
# directory separators are normalized. This happens before the output is
# sorted, to keep the ordering identical on all platforms.
prove_all(
    project="aggr.gpr",
    prover=None,
    refiners=[DirectorySeparatorRefiner(), *default_refiners()],
)
