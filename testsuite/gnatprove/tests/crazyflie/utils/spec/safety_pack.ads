with Types; use Types;
with IMU_Pack; use IMU_Pack;

package Safety_Pack
with SPARK_Mode
is
   --  Procedures and functions

   --  Deadband function
   function Dead_Band
     (Value     : Float;
      Threshold : Natural_Float) return Float is
     (if Value in -Threshold .. Threshold then
         0.0
      elsif Value > 0.0 then
         Value - Threshold
      elsif Value < 0.0 then
         Value + Threshold
      else
         Value);
   pragma Inline (Dead_Band);

   --  Saturate a Float value within a given range
   function Saturate
     (Value     : Float;
      Min_Value : Float;
      Max_Value : Float) return Float is
     (if Value < Min_Value then
         Min_Value
      elsif Value > Max_Value then
         Max_Value
      else
         Value);
   pragma Inline (Saturate);

   --  Saturate a T_Uint16 value within a given range
   function Saturate
     (Value     : T_Uint16;
      Min_Value : T_Uint16;
      Max_Value : T_Uint16) return T_Uint16 is
     (if Value < Min_Value then
         Min_Value
      elsif Value > Max_Value then
         Max_Value
      else
         Value);
   pragma Inline (Saturate);

   --  Truncate a 32-bit Integer into a 16-bit Integer
   function Truncate_To_T_Int16 (Value : Float) return T_Int16 is
     (if Value > Float (T_Int16'Last) then
           T_Int16'Last
      elsif Value < Float (T_Int16'First) then
           T_Int16'First
      else
           T_Int16 (Value));
   pragma Inline (Truncate_To_T_Int16);

   --  Ensure that a Float absolute value can't be inferior that 2^74
   --  to avoid having zero when doing
   --  a vector normalization (ie: Inv_Sqrt (X*X + Y*Y + Z*Z)
   function Lift_Away_From_Zero (X : T_Acc) return T_Acc_Lifted is
     (if X = 0.0 then
         0.0
      elsif X in -MIN_NON_ZERO_ACC .. 0.0 then
         -MIN_NON_ZERO_ACC
      elsif X in 0.0 .. MIN_NON_ZERO_ACC then
         MIN_NON_ZERO_ACC
      else
         X);
   pragma Inline (Lift_Away_From_Zero);

end Safety_Pack;
