with SPARK.Containers.Functional.Sets;
with Ada.Assertions; use Ada.Assertions;
with Ada.Containers;
use Ada.Containers;

with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

procedure Set with SPARK_Mode is
   package Containers is new SPARK.Containers.Functional.Sets
     (Element_Type => Integer);
   use Containers;
   S : Containers.Set := Empty_Set;

begin
   pragma Assert (Containers.Is_Empty (S));

   S := Containers.Add (S, 3);
   S := Containers.Add (S, 4);

   pragma Assert (not Containers.Is_Empty (S));
   pragma Assert (Containers.Contains (S, 3));
   pragma Assert (Containers.Contains (S, 4));
   pragma Assert (Containers.Length (S) = 2);

end Set;
