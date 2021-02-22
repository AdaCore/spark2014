with Ada.Containers.Formal_Doubly_Linked_Lists;
with Ada.Containers.Formal_Vectors;

package Loop_Types
  with SPARK_Mode
is
   subtype Index_T is Positive range 1 .. 1000;
   subtype Opt_Index_T is Natural range 0 .. 1000;
   subtype Component_T is Natural;

   type Arr_T is array (Index_T) of Component_T;

   package Vectors is new Ada.Containers.Formal_Vectors (Index_T, Component_T);
   subtype Vec_T is Vectors.Vector;

   package Lists is new Ada.Containers.Formal_Doubly_Linked_Lists (Component_T);
   subtype List_T is Lists.List;

end Loop_Types;
