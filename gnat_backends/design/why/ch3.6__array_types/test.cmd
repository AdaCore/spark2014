rm -rf why_out
mkdir why_out

gcc -c -gnatc arr.ads
why --dir why_out --alt-ergo ./arr_test.why
alt-ergo why_out/arr_test_why.why

gcc -c -gnatc unc.ads
why --dir why_out --alt-ergo ./unc_test.why
alt-ergo why_out/unc_test_why.why

# ??? for now, alt-ergo has some problems to manipulate
# multi-dimensional arrays.
# Do not run it on two_test.why. Run why only (to detect syntax errors).

gcc -c -gnatc two.ads
why --dir why_out --alt-ergo ./two_test.why

