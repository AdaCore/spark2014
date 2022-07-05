pragma Ada_2022;

with Text_IO; use Text_IO;

with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

procedure Test with SPARK_Mode => On
is
begin
   Put(Big_Integer'Image(1));
end Test;
