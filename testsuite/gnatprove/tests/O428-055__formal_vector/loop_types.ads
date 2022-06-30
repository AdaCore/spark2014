with SPARK.Containers.Formal.Doubly_Linked_Lists;
with SPARK.Containers.Formal.Vectors;

package Loop_Types
  with SPARK_Mode
is
   subtype Index_T is Positive range 1 .. 1000;
   subtype Component_T is Natural;

   type Arr_T is array (Index_T) of Component_T;

   package Vectors is new SPARK.Containers.Formal.Vectors (Index_T, Component_T);
   subtype Vec_T is Vectors.Vector;

   package Lists is new SPARK.Containers.Formal.Doubly_Linked_Lists (Component_T);
   subtype List_T is Lists.List;

end Loop_Types;
