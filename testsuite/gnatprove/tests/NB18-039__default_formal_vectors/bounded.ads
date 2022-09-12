with SPARK.Containers.Formal.Vectors;

package Bounded with
  SPARK_Mode
is

   package Vect is new SPARK.Containers.Formal.Vectors
     (Index_Type   => Positive,
      Element_Type => Integer);
   use Vect;

   procedure Test;

end Bounded;
