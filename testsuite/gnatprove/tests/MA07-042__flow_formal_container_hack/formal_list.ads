with SPARK.Containers.Formal.Vectors;

package Formal_List
is

   type Index_T is range 1 .. 100;

   package Vec is new SPARK.Containers.Formal.Vectors
     (Index_Type   => Index_T,
      Element_Type => Integer);

   type T is limited private
     with Default_Initial_Condition;

   type U is new Vec.Vector (100);

private

   type T is new Vec.Vector (100);

end Formal_List;
