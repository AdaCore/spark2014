package body Swap_Add_14
  with SPARK_Mode
is
   procedure Swap is
      Temporary: Integer;
   begin
      Temporary := X;
      X         := Y;
      Y         := Temporary;
   end Swap;

   function Add return Integer is (X + Y);
end Swap_Add_14;
