pragma SPARK_Mode;

procedure Test_Float is
   type RT is digits 6 range 0.0 .. 1000.0;

   procedure Add_Offset (X : in out RT) with
     Pre  => X <= 999.6,
     Post => X = X'Old + 0.4
   is
   begin
      X := X + 0.4;
   end Add_Offset;

   X : RT := 0.1;
begin
   Add_Offset (X);
   pragma Assert (X <= 1.0);
end Test_Float;
