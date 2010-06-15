rm -rf why_out
mkdir why_out

echo
echo "----------------"
echo "-- ENUM TYPES --"
echo "----------------"
echo

gcc -c -gnatc enum.ads
why --dir why_out --alt-ergo enum.why enum_test.why
alt-ergo why_out/enum_test_why.why

