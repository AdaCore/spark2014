with SPARK.Containers.Formal.Indefinite_Vectors;
with Ada.Containers; use Ada.Containers;

package Indefinite_Bounded_Tagged with
  SPARK_Mode
is
   type T is tagged record
      C : Integer;
   end record;

   subtype T_Class is T'Class;

   package Vect is new SPARK.Containers.Formal.Indefinite_Vectors
     (Index_Type   => Positive,
      Element_Type => T_Class,
      Max_Size_In_Storage_Elements => T'Size,
      Bounded      => True);
   use Vect;

   procedure Test;

end Indefinite_Bounded_Tagged;
