with Ada.Text_IO; use Ada.Text_IO;

procedure Pi_Compute with
  SPARK_Mode
is

   type Fixed is delta 2.0**(-20) range - (2.0**11) .. 2.0**11 - 1.0
     with Size => 32;

   function Leibniz_Fixed return Fixed
     with Post => Leibniz_Fixed'Result = 3.0418358
   is
      T1  : Fixed := 1.0;
      T2  : Fixed := 1.0 / 3.0;
      T3  : Fixed := 1.0 / 5.0;
      T4  : Fixed := 1.0 / 7.0;
      T5  : Fixed := 1.0 / 9.0;
      T6  : Fixed := 1.0 / 11.0;
      T7  : Fixed := 1.0 / 13.0;
      T8  : Fixed := 1.0 / 15.0;
      T9  : Fixed := 1.0 / 17.0;
      T10 : Fixed := 1.0 / 19.0;
      Res : Fixed;
   begin
      Res := 4 * (T1 - T2 + T3 - T4 + T5 - T6 + T7 - T8 + T9 - T10);
      pragma Assert (Res = 3.0418358);
      return Res;
   end Leibniz_Fixed;

   function Leibniz_Float return Float
     with Post => Leibniz_Float'Result = 3.0418395
   is
      T1  : Float := 1.0;
      T2  : Float := 1.0 / 3.0;
      T3  : Float := 1.0 / 5.0;
      T4  : Float := 1.0 / 7.0;
      T5  : Float := 1.0 / 9.0;
      T6  : Float := 1.0 / 11.0;
      T7  : Float := 1.0 / 13.0;
      T8  : Float := 1.0 / 15.0;
      T9  : Float := 1.0 / 17.0;
      T10 : Float := 1.0 / 19.0;
      Res : Float;
   begin
      Res := 4.0 * (T1 - T2 + T3 - T4 + T5 - T6 + T7 - T8 + T9 - T10);
      pragma Assert (Res = 3.0418395);
      return Res;
   end Leibniz_Float;

   function Shanks_Fixed return Fixed
     with Post => Shanks_Fixed'Result = 3.1412525177001953125
   is
      T1  : Fixed := 1.0;
      T2  : Fixed := 1.0 / 3.0;
      T3  : Fixed := 1.0 / 5.0;
      T4  : Fixed := 1.0 / 7.0;
      T5  : Fixed := 1.0 / 9.0;
      T6  : Fixed := 1.0 / 11.0;
      T7  : Fixed := 1.0 / 13.0;
      T8  : Fixed := 1.0 / 15.0;
      T9  : Fixed := 1.0 / 17.0;
      T10 : Fixed := 1.0 / 19.0;

      A1  : Fixed := T1;
      A2  : Fixed := A1 - T2;
      A3  : Fixed := A2 + T3;
      A4  : Fixed := A3 - T4;
      A5  : Fixed := A4 + T5;
      A6  : Fixed := A5 - T6;
      A7  : Fixed := A6 + T7;
      A8  : Fixed := A7 - T8;
      A9  : Fixed := A8 + T9;
      A10 : Fixed := A9 - T10;

      Num : Fixed := 4 * (A10 * A8 - A9 * A9);
      Den : Fixed := A10 - 2 * A9 + A8;
      Res : Fixed;
   begin
      Res := Num / Den;
      pragma Assert (Res = 3.1412525177001953125);
      return Res;
   end Shanks_Fixed;

   function Shanks_Float return Float
     with Post => Shanks_Float'Result = 3.1412551
   is
      T1  : Float := 1.0;
      T2  : Float := 1.0 / 3.0;
      T3  : Float := 1.0 / 5.0;
      T4  : Float := 1.0 / 7.0;
      T5  : Float := 1.0 / 9.0;
      T6  : Float := 1.0 / 11.0;
      T7  : Float := 1.0 / 13.0;
      T8  : Float := 1.0 / 15.0;
      T9  : Float := 1.0 / 17.0;
      T10 : Float := 1.0 / 19.0;

      A1  : Float := T1;
      A2  : Float := A1 - T2;
      A3  : Float := A2 + T3;
      A4  : Float := A3 - T4;
      A5  : Float := A4 + T5;
      A6  : Float := A5 - T6;
      A7  : Float := A6 + T7;
      A8  : Float := A7 - T8;
      A9  : Float := A8 + T9;
      A10 : Float := A9 - T10;

      Num : Float := 4.0 * (A10 * A8 - A9 * A9);
      Den : Float := A10 - 2.0 * A9 + A8;
      Res : Float;
   begin
      Res := Num / Den;
      pragma Assert (Res = 3.1412551);
      return Res;
   end Shanks_Float;

begin
   Put_Line ("Leibniz fixed value for Pi is" & Fixed'Image (Leibniz_Fixed));
   Put_Line ("Leibnitz float value for Pi is" & Float'Image (Leibniz_Float));
   Put_Line ("Shanks fixed value for Pi is" & Fixed'Image (Shanks_Fixed));
   Put_Line ("Shanks float value for Pi is" & Float'Image (Shanks_Float));
end Pi_Compute;
