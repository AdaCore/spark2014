function Rec (X : Integer) return Boolean
with SPARK_Mode => On,
     Pre  => X > 0,
     Post => Rec'Result and then Rec (X - 1);
