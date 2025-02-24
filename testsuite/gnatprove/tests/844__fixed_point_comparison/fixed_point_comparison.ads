
package Fixed_Point_Comparison with SPARK_Mode is

   type Foo is delta 1.0 / 128.0 range -100.0 .. 100.0;

   procedure Mutually_Exclusive (X, Y : Foo);

   procedure Mutually_Exclusive2 (X, Y : Foo);

end Fixed_Point_Comparison;
