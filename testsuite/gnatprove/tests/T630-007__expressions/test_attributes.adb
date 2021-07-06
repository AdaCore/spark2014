procedure Test_Attributes with SPARK_Mode is
   type S is new Integer with Alignment => 4;

   type My_Rec is record
      F, G : Integer;
   end record;
   for My_Rec use record
      F at 0 range 0 .. Integer'Size;
      G at 0 range Integer'Size + 1 .. 2 * Integer'Size + 1;
   end record;

   X : S := 0 with Alignment => 8;
   R : My_Rec := (1, 2);
   function Id (X : S) return S is (X);
begin
   pragma Assert (S'Alignment = Id(4));
   pragma Assert (X'Alignment = Id(8));
   pragma Assert (R.F'First_Bit = Id(0));
   pragma Assert (R.F'Last_Bit = Id(Integer'Size));
   pragma Assert (R.G'Position = Id(Integer'Size) / 8);
end Test_Attributes;
