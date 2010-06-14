rm -rf why_out
mkdir why_out

echo
echo "--------------------------"
echo "-- SIGNED INTEGER TYPES --"
echo "--------------------------"
echo

gcc -c -gnatc signed.ads
why --dir why_out --alt-ergo signed.why signed_test.why
alt-ergo why_out/signed_test_why.why

echo
echo "-------------------"
echo "-- MODULAR TYPES --"
echo "-------------------"
echo

gcc -c -gnatc modular.ads
why --dir why_out --alt-ergo modular.why modular_test.why
alt-ergo why_out/modular_test_why.why

echo
echo "=> This shows how 'Mod is expanded by the frontend":
echo

gcc -gnatG -S -o why_out/modular_mod.s modular_mod.adb

echo
echo "=> This shows how 'Modulus is expanded by the frontend:"
echo

gcc -gnatG -S -o why_out/modular_mod.s modular_modulus.adb
