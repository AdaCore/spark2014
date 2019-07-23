package utility_test is

   procedure Initialize_To_Please_Flow_Analysis(a : out Integer);

   procedure test_func_imported(a : Integer)
     with No_Return,
     Import => True,
     Convention => C,
     Global => null;

   procedure test_func_imported_read(a : Integer)
     with
     Import => True,
     Convention => C,
     Global => null;

   procedure test_func_imported_write(a : Integer)
     with
     Import => True,
     Convention => C,
     Global => null;

   procedure test_func_C(a : Integer)
     with No_Return;

   procedure test_read_C(a : out Integer);

   procedure test_write_C(a : Integer);

end utility_test;
