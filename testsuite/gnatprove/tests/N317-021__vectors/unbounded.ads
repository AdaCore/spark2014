with Ada.Containers.Formal_Vectors; use Ada.Containers;

package Unbounded with
  SPARK_Mode
is
   B : constant Boolean := False;

   package Vect is new Ada.Containers.Formal_Vectors
     (Index_Type   => Positive,
      Element_Type => Integer,
      Bounded      => not (if B then False else True));
   use Vect;

   procedure Test;

end Unbounded;
