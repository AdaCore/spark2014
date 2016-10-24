with Tree_Model; use Tree_Model;
use Tree_Model.D_Seq;
use Tree_Model.V_Set;
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

   function Root (T : Search_Tree) return Index_Type with
     Pre  => Size (T) /= 0;

   function Parent (T : Search_Tree; I : Index_Type) return Extended_Index_Type
   with Post => (if Size (T) = 0 then Parent'Result = 0);

   function Position (T : Search_Tree; I : Index_Type) return Direction with
     Pre  => Parent (T, I) /= 0;

   function Model (T : Search_Tree) return Model_Type with Ghost,
     Pre => Size (T) /= 0;

   function Peek (T : Search_Tree; I : Index_Type; D : Direction) return Extended_Index_Type with
     Pre  => Size (T) /= 0 and then Model (T) (I).K;

   function Values (T : Search_Tree) return Value_Set with Ghost,
     Post => (if Size (T) = 0 then Is_Empty (Values'Result));

   function Mem (T : Search_Tree; V : Natural) return Boolean with
     Post => Mem'Result = Mem (Values (T), V);

   procedure Insert
     (T : in out Search_Tree; V : Natural; I : out Extended_Index_Type)
     with
       Pre  => Size (T) < Max,
     Contract_Cases =>
       (Mem (Values (T), V) => I = 0
        and then Values (T) = Values (T'Old)
        and then (for all J in Index_Type => Parent (T, J) = Parent (T'Old, J))
        and then (for all J in Index_Type =>
                    (if Parent (T, J) /= 0
                     then Position (T, J) = Position (T'Old, J)))
        and then (for all J in Index_Type =>
                    (if Model (T) (J).K then Model (T'Old) (J).K))
        and then (for all J in Index_Type =>
                    (if Model (T'Old) (J).K then Model (T) (J).K)),
        Size (T) = 0               => I > 0
        and Size (T) = 1 and Root (T) = I
        and Is_Add (Values (T'Old), V, Values (T))
        and (for all I in Index_Type =>
               (if I /= Root (T) then not Model (T) (I).K))
        and (for all I in Index_Type => Parent (T, I) = Parent (T'Old, I)),
        others                     => I > 0 and then Model (T) (I).K
        and then Root (T) = Root (T'Old)
        and then Size (T) = Size (T)'Old + 1
        and then Is_Add (Values (T'Old), V, Values (T))
        and then (for all J in Index_Type =>
                    (if I /= J then Parent (T, J) = Parent (T'Old, J)))
        and then (for all J in Index_Type =>
                    (if I /= J and Parent (T, J) /= 0
                         then Position (T, J) = Position (T'Old, J)))
        and then (for all J in Index_Type =>
                    (if I /= J and Model (T) (J).K
                     then Model (T'Old) (J).K))
        and then (for all J in Index_Type =>
                    (if Model (T'Old) (J).K
                     then Model (T) (J).K and I /= J)));

   procedure Left_Rotate (T : in out Search_Tree; I : Index_Type) with
     Pre  => Size (T) > 0 and then Model (T) (I).K and then Peek (T, I, Right) /= 0,
     Post => Size (T) = Size (T)'Old
     and then (if Root (T)'Old /= I then Root (T) = Root (T)'Old
               else Root (T) = Peek (T'Old, I, Right))
     and then Parent (T, I) = Peek (T'Old, I, Right)
     and then Position (T, I) = Left
     and then Parent (T, Peek (T'Old, I, Right)) = Parent (T'Old, I)
     and then (if Root (T)'Old /= I
               then Position (T, Peek (T'Old, I, Right)) = Position (T'Old, I))
     and then (if Peek (T'Old, Peek (T'Old, I, Right), Left) /= 0
               then Parent (T, Peek (T'Old, Peek (T'Old, I, Right), Left)) = I
               and then Position (T, Peek (T'Old, Peek (T'Old, I, Right), Left)) = Right)
     and then (for all J in Index_Type =>
                 (if J /= I
                  and then (Parent (T'Old, J) /= I
                            or else Position (T'Old, J) = Left)
                  and then (Parent (T'Old, J) = 0
                            or else Parent (T'Old, Parent (T'Old, J)) /= I
                            or else Position (T'Old, Parent (T'Old, J)) = Left
                            or else Position (T'Old, J) = Right)
                  then Parent (T, J) = Parent (T'Old, J)))
     and then (for all J in Index_Type =>
                 (if J /= I
                  and then Parent (T'Old, J) /= 0
                  and then (Parent (T'Old, J) /= I
                            or else Position (T'Old, J) = Left)
                  and then (Parent (T'Old, Parent (T'Old, J)) /= I
                            or else Position (T'Old, Parent (T'Old, J)) = Left
                            or else Position (T'Old, J) = Right)
                  then Position (T, J) = Position (T'Old, J)))
     and then (for all J in Index_Type =>
                 (if Model (T) (J).K then Model (T'Old) (J).K))
     and then (for all J in Index_Type =>
                 (if Model (T'Old) (J).K then Model (T) (J).K))
     and then Values (T) = Values (T'Old);

   procedure Right_Rotate (T : in out Search_Tree; I : Index_Type) with
     Pre  => Size (T) > 0 and then Model (T) (I).K and then Peek (T, I, Left) /= 0,
     Post => Size (T) = Size (T)'Old
     and then (if Root (T)'Old /= I then Root (T) = Root (T)'Old
               else Root (T) = Peek (T'Old, I, Left))
     and then Parent (T, I) = Peek (T'Old, I, Left)
     and then Position (T, I) = Right
     and then Parent (T, Peek (T'Old, I, Left)) = Parent (T'Old, I)
     and then (if Root (T)'Old /= I
               then Position (T, Peek (T'Old, I, Left)) = Position (T'Old, I))
     and then (if Peek (T'Old, Peek (T'Old, I, Left), Right) /= 0
               then Parent (T, Peek (T'Old, Peek (T'Old, I, Left), Right)) = I
               and then Position (T, Peek (T'Old, Peek (T'Old, I, Left), Right)) = Left)
     and then (for all J in Index_Type =>
                 (if J /= I
                  and then (Parent (T'Old, J) /= I
                            or else Position (T'Old, J) = Right)
                  and then (Parent (T'Old, J) = 0
                            or else Parent (T'Old, Parent (T'Old, J)) /= I
                            or else Position (T'Old, Parent (T'Old, J)) = Right
                            or else Position (T'Old, J) = Left)
                  then Parent (T, J) = Parent (T'Old, J)))
     and then (for all J in Index_Type =>
                 (if J /= I
                  and then Parent (T'Old, J) /= 0
                  and then (Parent (T'Old, J) /= I
                            or else Position (T'Old, J) = Right)
                  and then (Parent (T'Old, Parent (T'Old, J)) /= I
                            or else Position (T'Old, Parent (T'Old, J)) = Right
                            or else Position (T'Old, J) = Left)
                  then Position (T, J) = Position (T'Old, J)))
     and then (for all J in Index_Type =>
                 (if Model (T) (J).K then Model (T'Old) (J).K))
     and then (for all J in Index_Type =>
                 (if Model (T'Old) (J).K then Model (T) (J).K))
     and then Values (T) = Values (T'Old);
private

   type Value_Array is array (Index_Type) of Natural;

   type Search_Tree is record
      Root   : Extended_Index_Type := 0;
      Struct : Forest;
      Values : Value_Array;
   end record
     with Type_Invariant =>
       ((if Size (Struct) = 0 then Root = 0
          else
            Root /= 0 and then Valid_Root (Struct, Root)
            and then Ordered_Leafs (Struct, Root, Values)));

   function Ordered_Leafs (F : Forest; Root : Index_Type; Values : Value_Array)
                           return Boolean with Ghost,
   Pre => Valid_Root (F, Root);

   function Model (T : Search_Tree) return Model_Type is
     (Model (T.Struct, T.Root));

   function Size (T : Search_Tree) return Extended_Index_Type is
     (Size (T.Struct));

   function Root (T : Search_Tree) return Index_Type is
     (T.Root);

   function Parent (T: Search_Tree; I : Index_Type) return Extended_Index_Type is
      (Parent (T.Struct, I));

   function Position (T: Search_Tree; I : Index_Type) return Direction is
      (Position (T.Struct, I));

   function Peek (T : Search_Tree; I : Index_Type; D : Direction) return Extended_Index_Type is
      (Peek (T.Struct, I, D));
end Search_Trees;
