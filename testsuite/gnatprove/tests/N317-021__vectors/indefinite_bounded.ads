with Ada.Containers.Formal_Indefinite_Vectors; use Ada.Containers;

package Indefinite_Bounded with
  SPARK_Mode
is
   package Vect is new Ada.Containers.Formal_Indefinite_Vectors
     (Index_Type   => Positive,
      Element_Type => Integer,
      Max_Size_In_Storage_Elements => Integer'Size,
      Bounded      => True);
   use Vect;

   procedure Test;

end Indefinite_Bounded;
