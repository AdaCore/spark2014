with Types; use Types;
with IMU_Pack; use IMU_Pack;

package Safety_Pack
  with SPARK_Mode
is
   --  Procedures and functions

   --  Deadband function
   function Dead_Band
     (Value     : Float;
      Threshold : Positive_Float) return Float

     with
       Contract_Cases => ((Value in -Threshold .. Threshold) =>
                                Dead_Band'Result = 0.0,
                          Value > Threshold                  =>
                            Dead_Band'Result = Value - Threshold,
                          Value < -Threshold                 =>
                            Dead_Band'Result = Value + Threshold);
   pragma Inline (Dead_Band);

   --  Saturate a Float value within a given range
   function Saturate
     (Value     : Float;
      Min_Value : Float;
      Max_Value : Float) return Float
     with
       Post => (if Value < Min_Value then
                  Saturate'Result = Min_Value
                elsif Value > Max_Value then
                  Saturate'Result = Max_Value
                else
                  Saturate'Result = Value);

   pragma Inline (Saturate);

   --  Saturate a T_Uint16 value within a given range
   function Saturate
     (Value     : T_Uint16;
      Min_Value : T_Uint16;
      Max_Value : T_Uint16) return T_Uint16
     with
        Post => (if Value < Min_Value then
                  Saturate'Result = Min_Value
                elsif Value > Max_Value then
                  Saturate'Result = Max_Value
                else
                  Saturate'Result = Value);
   pragma Inline (Saturate);

   --  Truncate a 32-bit Integer into a 16-bit Integer
   function Truncate_To_T_Int16 (Value : Float) return T_Int16;
   pragma Inline (Truncate_To_T_Int16);

   --  Round a float value to 2^74 or -2.74 to avoid having zero when doing
   --  a vector normalization (ie: Inv_Sqrt (X*X + Y*Y + Z*Z)
   function Lift_Away_From_Zero (X : T_Acc) return T_Acc_Lifted
     with Contract_Cases => (X = 0.0 => Lift_Away_From_Zero'Result = 0.0,
                             X /= 0.0 => Lift_Away_From_Zero'Result /= 0.0);
   pragma Inline (Lift_Away_From_Zero);

end Safety_Pack;
