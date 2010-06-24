rm -rf why_out
mkdir why_out

gcc -c -gnatc fixed.ads
why --dir why_out --alt-ergo ./real.why ./fixed.why
alt-ergo why_out/fixed_why.why
