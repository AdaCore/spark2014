rm -rf why_out
mkdir why_out

gcc -c -gnatc rec.ads
why --dir why_out --alt-ergo ./rec_test.why
alt-ergo why_out/rec_test_why.why

