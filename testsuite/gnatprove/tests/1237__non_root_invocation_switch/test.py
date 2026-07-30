from test_support import DirectorySeparatorRefiner, default_refiners, prove_all

# The warning mentions the relative path of a non-root project, so directory
# separators need to be normalized to compare against the expected output.
prove_all(refiners=[*default_refiners(), DirectorySeparatorRefiner()])
