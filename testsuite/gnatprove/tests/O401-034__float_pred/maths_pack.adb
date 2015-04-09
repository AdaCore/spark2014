with Ada.Unchecked_Conversion;
with Interfaces; use Interfaces;

package body Maths_Pack
  with SPARK_Mode
is

   function Inv_Sqrt (X : Float) return Float is
      Half_X    : Float := 0.5 * X;
      Y         : Float := X;
      Magic_Num : Unsigned_32 := 16#5f3759df#;
      I         : Unsigned_32;
      function Float_To_Unsigned_32 is new Ada.Unchecked_Conversion
        (Float, Unsigned_32);
      function Unsigned_32_To_Float is new Ada.Unchecked_Conversion
        (Unsigned_32, Float);
   begin
      I := Float_To_Unsigned_32 (Y);
      I := Magic_Num - Shift_Right (I, 1);
      Y := Unsigned_32_To_Float (I);
      Y := Y * (1.5 - (Half_X * Y * Y));
      return Y;
   end Inv_Sqrt;



end Maths_Pack;
