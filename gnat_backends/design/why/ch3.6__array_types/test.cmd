rm -rf why_out
mkdir why_out

gcc -c -gnatc arr.ads
why --dir why_out --alt-ergo ./arr_test.why
alt-ergo why_out/arr_test_why.why

gcc -c -gnatc unc.ads
why --dir why_out --alt-ergo ./unc_test.why
alt-ergo why_out/unc_test_why.why
