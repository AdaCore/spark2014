with abstract_state_package;

package body utility_test is

   procedure Initialize_To_Please_Flow_Analysis(a : out Integer) is null
     with SPARK_Mode => Off;

   procedure test_read_C( a : out Integer )
   is
   begin
      Initialize_To_Please_Flow_Analysis(a);
      test_func_imported_read(a);
      abstract_state_package.state_change;--
   end test_read_C;

   procedure test_write_C( a : Integer )
   is
   begin
      test_func_imported_write(a);
      abstract_state_package.state_change;--
   end test_write_C;

   procedure test_func_C( a : Integer )
   is
   begin
      test_func_imported(a);
   end test_func_C;

end utility_test;
