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

   type List_Cell;
   type List_Acc is access List_Cell;
   type List_Cell is record
      Value : Component_T;
      Next  : List_Acc;
   end record;

   function At_End
     (L : access constant List_Cell) return access constant List_Cell
   is (L)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   type Property is access function (X : Component_T) return Boolean;

   function For_All_List
     (L : access constant List_Cell;
      P : not null Property) return Boolean
   is
     (L = null or else (P (L.Value) and then For_All_List (L.Next, P)))
   with Annotate => (GNATprove, Terminating);
   pragma Annotate (GNATprove, False_Positive, "is recursive",
                    "The recursive call occurs on a strictly smaller list");
   pragma Annotate (GNATprove, False_Positive, "call via access-to-subprogram",
                    "We only call For_All_List on terminating functions");

   type Relation is access function (X, Y : Component_T) return Boolean;

   function For_All_List
     (L1, L2 : access constant List_Cell;
      P      : not null Relation) return Boolean
   is
     ((L1 = null) = (L2 = null)
      and then
        (if L1 /= null
         then P (L1.Value, L2.Value)
         and then For_All_List (L1.Next, L2.Next, P)))
   with Annotate => (GNATprove, Terminating);
   pragma Annotate (GNATprove, False_Positive, "is recursive",
                    "The recursive call occurs on a strictly smaller lists");
   pragma Annotate (GNATprove, False_Positive, "call via access-to-subprogram",
                    "We only call For_All_List on terminating functions");

end Loop_Types;
