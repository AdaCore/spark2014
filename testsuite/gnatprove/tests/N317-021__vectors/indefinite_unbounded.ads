with Ada.Containers.Formal_Indefinite_Vectors; use Ada.Containers;

package Indefinite_Unbounded with
  SPARK_Mode
is
   B : constant Boolean := False;

   package Vect is new Ada.Containers.Formal_Indefinite_Vectors
     (Index_Type   => Positive,
      Element_Type => Integer,
      Max_Size_In_Storage_Elements => Integer'Size,
      Bounded      => not (if B then False else True));
   use Vect;

   procedure Test;

end Indefinite_Unbounded;
