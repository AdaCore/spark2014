package Fixed_Point_Unary with SPARK_Mode is

   type Foo is delta 0.5 range -100.0 .. 100.0;

   procedure Fixed_Point_Unary (X, Y : in out Foo)
     with Pre => X >= abs Y,
     Post => X > Y;

   type Bar is delta 0.5 range -100.0 .. 150.0;

   function Opposite (Y : Bar) return Bar is
     (-Y);

end Fixed_Point_Unary;
