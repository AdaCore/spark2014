package body Safety_Pack
  with SPARK_Mode
is

   function Saturate
     (Value     : Float;
      Min_Value : Float;
      Max_Value : Float) return Float is
      Res : Float := Value;
   begin
      if Value < Min_Value then
         Res := Min_Value;
      elsif Value > Max_Value then
         Res := Max_Value;
      end if;
      return Res;
   end Saturate;

   function Saturate
     (Value     : T_Uint16;
      Min_Value : T_Uint16;
      Max_Value : T_Uint16) return T_Uint16 is
      Res : T_Uint16 := Value;
   begin
      if Value < Min_Value then
         Res := Min_Value;
      elsif Value > Max_Value then
         Res := Max_Value;
      end if;
      return Res;
   end Saturate;

   function Dead_Band
     (Value     : Float;
      Threshold : Positive_Float) return Float is
      Res : Float := Value;
   begin
      if Value in -Threshold .. Threshold then
         Res := 0.0;
      elsif Value > 0.0 then
         Res := Res - Threshold;
      elsif Value < 0.0 then
         Res := Res + Threshold;
      end if;

      return Res;
   end Dead_Band;

   function Truncate_To_T_Int16 (Value : Float) return T_Int16 is
      Res : T_Int16;
   begin
      if Value > Float (T_Int16'Last) then
         Res :=  T_Int16'Last;
      elsif Value < Float (T_Int16'First) then
         Res :=  T_Int16'First;
      else
         Res := T_Int16 (Value);
      end if;

      return Res;
   end Truncate_To_T_Int16;

   function Lift_Away_From_Zero (X : T_Acc) return T_Acc_Lifted is
      Res : T_Acc_Lifted;
   begin
      if X = 0.0 then
         Res := 0.0;
      elsif X in -MIN_NON_ZERO_ACC .. 0.0 then
         Res := -MIN_NON_ZERO_ACC;
      elsif X in 0.0 .. MIN_NON_ZERO_ACC then
         Res := MIN_NON_ZERO_ACC;
      else
         Res := X;
      end if;

      return Res;
   end Lift_Away_From_Zero;

end Safety_Pack;
