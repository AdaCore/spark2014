with utility_test;

procedure test_func( a : Integer ) with No_Return
is
   b : Integer;
begin
   utility_test.test_read_C(b);
   b := b+10;
   utility_test.test_write_C(b);
   utility_test.test_func_C(a);
end test_func;
