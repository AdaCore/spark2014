package Slice_Test_2
  with SPARK_Mode => On
is

   type Day is (Monday, Tuesday, Wednesday, Thursday, Friday, Saturday, Sunday);
   type Schedule is array (Day) of Boolean;

   procedure Dynamic_Slice_Bound (A : in out Schedule; D : in Day)
     with Pre => D = Wednesday;

end Slice_Test_2;
