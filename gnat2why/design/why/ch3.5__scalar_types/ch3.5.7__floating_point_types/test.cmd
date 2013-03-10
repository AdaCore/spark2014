rm -rf why_out
mkdir why_out

gcc -c -gnatc floats.ads
why --dir why_out --alt-ergo ./floats.why
alt-ergo why_out/floats_why.why
