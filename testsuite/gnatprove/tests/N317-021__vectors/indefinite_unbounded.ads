with SPARK.Containers.Formal.Unbounded_Vectors;
with Ada.Containers; use Ada.Containers;

package Indefinite_Unbounded with
  SPARK_Mode
is
   B : constant Boolean := False;

   package Vect is new SPARK.Containers.Formal.Unbounded_Vectors
     (Index_Type   => Positive,
      Element_Type => Integer);
   use Vect;

   procedure Test;

end Indefinite_Unbounded;
