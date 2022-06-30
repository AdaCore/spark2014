with SPARK.Containers.Formal.Indefinite_Vectors;
with Ada.Containers; use Ada.Containers;

package Indefinite_Bounded with
  SPARK_Mode
is
   package Vect is new SPARK.Containers.Formal.Indefinite_Vectors
     (Index_Type   => Positive,
      Element_Type => Integer,
      Max_Size_In_Storage_Elements => Integer'Size,
      Bounded      => True);
   use Vect;

   procedure Test;

end Indefinite_Bounded;
