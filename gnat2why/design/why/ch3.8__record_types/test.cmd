rm -rf why_out
mkdir why_out

gcc -c -gnatc rec.ads
why --dir why_out --alt-ergo ./rec_test.why
alt-ergo why_out/rec_test_why.why

gcc -c -gnatc var.ads
gcc -c -gnatc -gnat12 var_test.adb
why --dir why_out --alt-ergo ./var_test.why
alt-ergo why_out/var_test_why.why
