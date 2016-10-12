with Tree_Model; use Tree_Model;
use Tree_Model.D_Seq;
with Conts; use Conts;
with Binary_Trees; use Binary_Trees;

--  This package provides an implementation of binary search trees on top of
--  the Forest type defined in Binary_Trees. A search tree is a forest with
--  a root and a natural value per node. It has an invariant stating that
--  values of the nodes of the tree are ordered. It provides primitives for
--  inserting a value in the tree and for searching the tree for a given
--  value. It also provides Rotate primitives that can be used to balance the
--  search tree.

package Search_Trees with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Search_Tree is private with Default_Initial_Condition =>
     Size (Search_Tree) = 0;

   function Size (T : Search_Tree) return Extended_Index_Type;

   function Root (T : Search_Tree) return Extended_Index_Type;

   function Parent (T : Search_Tree; I : Index_Type) return Extended_Index_Type;

   function Position (T : Search_Tree; I : Index_Type) return Direction with
     Pre  => Parent (T, I) /= 0;

   function Model (T : Search_Tree) return Model_Type with Ghost,
     Pre => Size (T) /= 0;

   function Peek (T : Search_Tree; I : Index_Type; D : Direction) return Extended_Index_Type with
     Pre  => Size (T) /= 0 and then Model (T) (I).K;

   function Value (T : Search_Tree; I : Index_Type) return Natural with
     Ghost,
     Pre => Size (T) /= 0 and then Model (T) (I).K;

   function Mem (T : Search_Tree; V : Natural) return Boolean with
     Post => Mem'Result =
       (Size (T) /= 0 and then
          (for some I in Index_Type => Model (T) (I).K
           and then Value (T, I) = V));

   procedure Insert
     (T : in out Search_Tree; V : Natural; I : out Extended_Index_Type)
     with
       Pre  => Size (T) < Max,
     Contract_Cases =>
       (Mem (T, V)   => I = 0 and T = T'Old,
        Size (T) = 0 => I > 0
        and Size (T) = 1 and Model (T) (I).K and Value (T, I) = V,
        others       => I > 0
        and then Size (T) = Size (T)'Old + 1
        and then Model (T) (I).K
        and then not Model (T'Old) (I).K
        and then Value (T, I) = V
        and then
          (for all J in Index_Type =>
             (if I /= J and Model (T) (J).K
              then Model (T) (J).A = Model (T'Old) (J).A))
        and then
          (for all J in Index_Type =>
             (if I /= J and Model (T) (J).K
                  then Value (T, J) = Value (T'Old, J)))
        and then (for all J in Index_Type =>
                    (if Model (T) (J).K and I /= J
                         then Parent (T, J) = Parent (T'Old, J)))
        and then (for all J in Index_Type =>
                    (if Model (T) (J).K and I /= J and Parent (T, J) /= 0
                         then Position (T, J) = Position (T'Old, J))));

   procedure Left_Rotate (T : in out Search_Tree; I : Index_Type) with
     Pre  => Size (T) > 0 and then Model (T) (I).K and then Peek (T, I, Right) /= 0,
     Post => Model (T) (I).K;

   procedure Right_Rotate (T : in out Search_Tree; I : Index_Type) with
     Pre  => Size (T) > 0 and then Model (T) (I).K and then Peek (T, I, Left) /= 0,
     Post => Model (T) (I).K;
private

   type Value_Array is array (Index_Type) of Natural;

   type Search_Tree is record
      Root   : Extended_Index_Type := 0;
      Struct : Forest;
      Values : Value_Array;
   end record
     with Type_Invariant => Ordered_Leafs (Search_Tree);

   function Ordered_Leafs (T : Search_Tree) return Boolean with Ghost;

   function Model (T : Search_Tree) return Model_Type is
     (Model (T.Struct, T.Root));

   function Size (T : Search_Tree) return Extended_Index_Type is
     (Size (T.Struct));

   function Root (T : Search_Tree) return Extended_Index_Type is
     (T.Root);

   function Parent (T: Search_Tree; I : Index_Type) return Extended_Index_Type is
      (Parent (T.Struct, I));

   function Position (T: Search_Tree; I : Index_Type) return Direction is
      (Position (T.Struct, I));

   function Peek (T : Search_Tree; I : Index_Type; D : Direction) return Extended_Index_Type is
      (Peek (T.Struct, I, D));
end Search_Trees;
