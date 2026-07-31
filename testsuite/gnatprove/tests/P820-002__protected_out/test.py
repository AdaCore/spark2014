from test_support import DirectorySeparatorRefiner, default_refiners, prove_all

# The SPARK_Mode violations and the non-root project warnings mention files of a
# subproject by a relative path, so directory separators are normalized. This
# happens before the output is sorted, to keep the ordering identical on all
# platforms.
prove_all(
    opt=["-XTARGET=SPARK"],
    refiners=[DirectorySeparatorRefiner(), *default_refiners()],
)
