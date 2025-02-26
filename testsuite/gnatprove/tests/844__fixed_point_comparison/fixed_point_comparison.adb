package body Fixed_Point_Comparison with SPARK_Mode is

   procedure Mutually_Exclusive (X, Y : Foo) is
   begin
      pragma Assert ((X > Y) and (X <= Y));
   end;

   procedure Mutually_Exclusive2 (X, Y : Foo) is
   begin
      pragma Assert ((X < Y) and (X >= Y));
   end;

end Fixed_Point_Comparison;
