rm -rf why_out
mkdir why_out

modular_dir=../ch3.5.4__integer_types

echo
echo "-------------------"
echo "-- MODULAR TYPES --"
echo "-------------------"
echo

gcc -c -gnatc modular_ops.adb -I${modular_dir}
why --dir why_out --alt-ergo ${modular_dir}/modular.why \
 modular_ops.why modular_ops_test.why
alt-ergo why_out/modular_ops_test_why.why

