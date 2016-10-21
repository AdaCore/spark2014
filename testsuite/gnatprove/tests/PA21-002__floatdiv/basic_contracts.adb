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

end Basic_Contracts;
