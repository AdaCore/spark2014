with Ada.Assertions; use Ada.Assertions;
with SPARK.Containers.Functional.Maps;
with Ada.Containers; use Ada.Containers;

with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

procedure Map with SPARK_Mode is
   package Containers is new  SPARK.Containers.Functional.Maps
     (Key_Type     => Positive,
      Element_Type => Natural);

   Map_Instance : Containers.Map := Containers.Empty_Map;
begin
   --  To make sure that the map is actually empty

   pragma Assert (Containers.Length (Map_Instance) = 0);
   pragma Assert (Containers.Is_Empty (Map_Instance));
end Map;
