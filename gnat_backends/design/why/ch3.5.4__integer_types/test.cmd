rm -rf why_out
mkdir why_out

# signed integer types
gcc -c -gnatc signed.ads
why --dir why_out --alt-ergo signed.why signed_test.why
alt-ergo why_out/signed_test_why.why

# modular types
gcc -c -gnatc modular.ads
why --dir why_out --alt-ergo modular.why modular_test.why
alt-ergo why_out/modular_test_why.why
