package body Basic_Contracts is
 pragma SPARK_Mode(On);

 function Increment (Item : Integer) return Integer is (Item + 1);

 function Average (Numerator : Integer;
 Denominator : Integer) return Float is
   subtype Pos_Float is Float range 1.0 .. Float'Last;
   subtype Non_Neg_Float is Float range 0.0 .. Float'Last;
   Num : constant Non_Neg_Float := Non_Neg_Float (Numerator);
   Den : constant Pos_Float := Pos_Float (Denominator);
 begin
 return Num / Den;
 end Average;

   function Average_Orig (Numerator : Integer;
                          Denominator : Integer) return Float
   is
      Res : Float;
   begin
      pragma Assert (Float(Numerator) >= 0.0);
      pragma Assert (Float(Denominator) >= 1.0);
      Res := Float (Numerator) / Float (Denominator);
      pragma Assert (Res >= 0.0);
      return Res;
   end Average_Orig;

   function Average_Float (Numerator : Float;
                           Denominator : Float) return Float
   is
      Res : Float;
   begin
      --pragma Assert (Numerator >= 0.0);
      --pragma Assert (Denominator >= 1.0);
      Res := Numerator / Denominator;
      --pragma Assert (Res >= 0.0);
      return Res;
   end Average_Float;

end Basic_Contracts;
