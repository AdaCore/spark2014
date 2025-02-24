package body Fixed_Point_Unary with SPARK_Mode is

   procedure Fixed_Point_Unary (X, Y : in out Foo) is
   begin
      Y := -Y;
   end Fixed_Point_Unary;

end Fixed_Point_Unary;
