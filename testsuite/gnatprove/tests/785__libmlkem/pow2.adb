package body Pow2
  with SPARK_Mode
is

   procedure Stride_Product (I : Bit_Index) is
      Count : constant Natural := 2 ** I;
      Len   : constant Natural := 2 ** (7 - I);
   begin
      pragma Assert (Count * Len = 128);
   end Stride_Product;

   procedure Width_From_Stride (I : Bit_Index) is
      Len : constant Natural := 2 ** (7 - I);
   begin
      pragma Assert (2 ** I * Len = 128);
   end Width_From_Stride;

   procedure Inner_Start_Bound (I : Bit_Index; J : Natural) is
      Len : constant Natural := 2 ** (7 - I);
   begin
      pragma Assert (J * 2 * Len <= 252);
   end Inner_Start_Bound;

end Pow2;
