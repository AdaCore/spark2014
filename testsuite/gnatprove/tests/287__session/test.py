from test_support import DirectorySeparatorRefiner, default_refiners, prove_all

prove_all(refiners=[*default_refiners(), DirectorySeparatorRefiner()])
