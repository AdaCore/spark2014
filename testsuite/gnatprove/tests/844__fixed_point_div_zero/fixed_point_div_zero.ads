package Fixed_Point_Div_Zero with SPARK_Mode is

   type Foo is delta 1.0 / 128.0 range -100.0 .. 100.0;

   function Div (X, Y : Foo) return Foo is
     (X / Y);

   function Div_Int (X, Y : Foo) return Integer is
     (Integer (X) / Integer (Y)) with Pre => Y /= 0.0;

   function Div_Skewd (X : Foo) return Foo is
     (X / (X - 1.0));

end Fixed_Point_Div_Zero;
