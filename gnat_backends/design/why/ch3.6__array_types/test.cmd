rm -rf why_out
mkdir why_out

gcc -c -gnatc arr.ads
gcc -c -gnatc arr_test.adb
why --dir why_out --alt-ergo ./arr_test.why
alt-ergo why_out/arr_test_why.why

gcc -c -gnatc unc.ads
gcc -c -gnatc unc_test.adb
why --dir why_out --alt-ergo ./unc_test.why
alt-ergo why_out/unc_test_why.why

gcc -c -gnatc two.ads
gcc -c -gnatc two_test.adb
why --dir why_out --alt-ergo ./two_test.why
alt-ergo why_out/two_test_why.why

