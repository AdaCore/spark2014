with Pack; use Pack;
procedure Test_Rec with SPARK_Mode is

   function Id (X : My_Arr) return My_Arr with Pre => True;
   function Id (X : My_Arr) return My_Arr is
   begin
      return X;
   end Id;

   X : My_Arr := (1, 2, 3);
   M : My_Arr := Id (X);

   package Nested is
      pragma Assert (Sum (M) <= 100 * M'Length);
   end Nested;
begin
   pragma Assert (Sum (X) <= 300);
   pragma Assert (Sum (X) = 6);
   pragma Assert (Sum (M) <= 100 * M'Length);
end;
