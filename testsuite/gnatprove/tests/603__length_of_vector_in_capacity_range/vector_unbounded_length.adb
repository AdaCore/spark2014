with SPARK.Containers.Formal.Unbounded_Vectors;
with Ada.Containers; use Ada.Containers;
procedure Vector_Unbounded_Length is
   type Rng is range 0 .. 50000;
   subtype Index is Rng range 1 .. 3000;
   package V is new SPARK.Containers.Formal.Unbounded_Vectors
     (Index_Type    => Index,
      Element_Type  => Integer);
   procedure Test (X : V.Vector) with Global => null, Post => True;

   procedure Test (X : V.Vector) is
   begin
      pragma Assert (V.Length (X) <= 3000);
   end Test;
begin
   null;
end Vector_Unbounded_Length;
