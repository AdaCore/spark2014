rm -rf why_out
mkdir why_out

why --dir why_out --alt-ergo ./bools.why
alt-ergo why_out/bools_why.why
