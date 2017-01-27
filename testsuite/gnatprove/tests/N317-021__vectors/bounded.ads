with Ada.Containers.Formal_Vectors; use Ada.Containers;

package Bounded with
  SPARK_Mode
is
   package Vect is new Ada.Containers.Formal_Vectors
     (Index_Type   => Positive,
      Element_Type => Integer,
      Bounded      => True);
   use Vect;

   procedure Test;

end Bounded;
