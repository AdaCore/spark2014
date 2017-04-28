with Tree_Model; use Tree_Model;
use Tree_Model.D_Seq;
use Tree_Model.V_Set;
with Ada.Containers; use Ada.Containers;
with Binary_Trees; use Binary_Trees;

--  This package provides an implementation of binary search trees on top of the
--  Forest type defined in Binary_Trees. A search tree is a forest with a root
--  and a natural value per node. It has an invariant stating that values of the
--  nodes of the tree are ordered. It provides primitives for inserting a value
--  in the tree and for searching the tree for a given value. It also provides
--  Rotate primitives that can be used to balance the search tree.

package Search_Trees with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Search_Tree is private with Default_Initial_Condition =>
     Size (Search_Tree) = 0;

   function Size (T : Search_Tree) return Extended_Index_Type;

   function Root (T : Search_Tree) return Index_Type with
     Pre => Size (T) /= 0;

   function Parent (T : Search_Tree; I : Index_Type) return Extended_Index_Type with
     Post => (if Size (T) = 0 then Parent'Result = Empty);

   function Position (T : Search_Tree; I : Index_Type) return Direction with
     Pre => Parent (T, I) /= Empty;

   function Model (T : Search_Tree) return Model_Type with
     Ghost,
     Pre => Size (T) /= 0;

   function Peek (T : Search_Tree; I : Index_Type; D : Direction) return Extended_Index_Type with
     Pre => Size (T) /= 0 and then Model (T) (I).K;

   function Values (T : Search_Tree) return Value_Set with
     Ghost,
     Post => (if Size (T) = 0 then Is_Empty (Values'Result));

   function Contains (T : Search_Tree; V : Natural) return Boolean with
     Post => Contains'Result = Contains (Values (T), V);

   procedure Insert
     (T : in out Search_Tree; V : Natural; I : out Extended_Index_Type)
   with
     Pre  =>
       --  There are free nodes to use
       Size (T) < Max,
     Contract_Cases =>

       --  Case 1: V is already in the tree. Return the empty node in I. All
       --  values in the tree, as well as the values of positions and parent
       --  link, are preserved. We cannot state simply that T = T'Old as this
       --  would be the component-wise equality of SPARK, not the logical
       --  equality of T and T'Old. Instead, state explicitly which properties
       --  are preserved.
       (Contains (Values (T), V) =>
          I = Empty
          and then Values (T) = Values (T'Old)
          and then (for all J in Index_Type => Parent (T, J) = Parent (T'Old, J))
          and then (for all J in Index_Type =>
                     (if Parent (T, J) /= Empty
                      then Position (T, J) = Position (T'Old, J)))
          and then (for all J in Index_Type =>
                     (if Model (T) (J).K then Model (T'Old) (J).K))
          and then (for all J in Index_Type =>
                     (if Model (T'Old) (J).K then Model (T) (J).K))
          and then (for all J in Index_Type =>
                        (for all D in Direction =>
                           (if Model (T) (J).K then
                                Peek (T'Old, J, D) = Peek (T, J, D)))),

        --  Case 2: the tree is empty. Return a singleton tree in T, whose root
        --  is I. Value V is added to the previous (empty) set of values. The
        --  value of the parent link is preserved for all nodes.
        Size (T) = 0 =>
          I /= Empty
          and then Size (T) = 1
          and then Root (T) = I
          and then Is_Add (Values (T'Old), V, Values (T))
          and then (for all I in Index_Type =>
                     (if I /= Root (T) then not Model (T) (I).K))
          and then (for all I in Index_Type => Parent (T, I) = Parent (T'Old, I)),

        --  Case 3: the tree is not empty and V is not in it. Return in T a tree
        --  with the same root, the same nodes expect a new node I, whose size
        --  has been increased by 1. Value V is added to the previous set of
        --  values. The value of position and parent link is preserved for all
        --  nodes except I.
        others =>
          I /= Empty
          and then Model (T) (I).K
          and then Root (T) = Root (T'Old)
          and then Size (T) = Size (T)'Old + 1
          and then Is_Add (Values (T'Old), V, Values (T))
          and then (for all J in Index_Type =>
                     (if I /= J then Parent (T, J) = Parent (T'Old, J)))
          and then (for all J in Index_Type =>
                     (if I /= J and Parent (T, J) /= Empty
                      then Position (T, J) = Position (T'Old, J)))
          and then (for all J in Index_Type =>
                     (if I /= J and Model (T) (J).K
                      then Model (T'Old) (J).K))
          and then (for all J in Index_Type =>
                     (if Model (T'Old) (J).K
                      then Model (T) (J).K and I /= J))
          and then (for all D in Direction => Peek (T, I, D) = 0)
          and then Peek (T'Old, Parent (T, I), Position (T, I)) = 0
          and then (for all J in Index_Type =>
                        (for all D in Direction =>
                           (if Model (T) (J).K
                            and I /= J
                            and (J /= Parent (T, I) or D /= Position (T, I))
                            then
                                Peek (T'Old, J, D) = Peek (T, J, D)))));

   procedure Left_Rotate (T : in out Search_Tree; I : Index_Type) with
     Pre  =>
       --  The tree is not empty
       Size (T) > 0

       --  I is in the tree
       and then Model (T) (I).K

       --  I has a right child
       and then Peek (T, I, Right) /= Empty,
     Post =>
       --  The size of the tree is preserved
       Size (T) = Size (T)'Old

       --  When rotating on the root, the right child of the root becomes the
       --  new root, otherwise the root is preserved.
       and then (if Root (T)'Old /= I then Root (T) = Root (T)'Old
                 else Root (T) = Peek (T'Old, I, Right))

       --  The right child of I becomes it parent, of which I becomes the left
       --  child.
       and then Parent (T, I) = Peek (T'Old, I, Right)
       and then Position (T, I) = Left

       --  The parent of I becomes the parent of its previous right child, and
       --  unless I was root, as the same child (left or right).
       and then Parent (T, Peek (T'Old, I, Right)) = Parent (T'Old, I)
       and then (if Root (T)'Old /= I
                 then Position (T, Peek (T'Old, I, Right)) = Position (T'Old, I))

       --  During the rotation, the subtree located at the left child of the
       --  right child of I becomes the right child of I.
       and then (if Peek (T'Old, Peek (T'Old, I, Right), Left) /= Empty
                 then Parent (T, Peek (T'Old, Peek (T'Old, I, Right), Left)) = I
                   and then Position (T, Peek (T'Old, Peek (T'Old, I, Right), Left)) = Right)

       --  Except for I, its right child, and the left child of its right child,
       --  the parent link is preserved.
       and then (for all J in Index_Type =>
                  (if J /= I
                     and then (Parent (T'Old, J) /= I
                               or else Position (T'Old, J) = Left)
                     and then (Parent (T'Old, J) = Empty
                               or else Parent (T'Old, Parent (T'Old, J)) /= I
                               or else Position (T'Old, Parent (T'Old, J)) = Left
                               or else Position (T'Old, J) = Right)
                   then Parent (T, J) = Parent (T'Old, J)))

       --  Except for I, its right child, and the left child of its right child,
       --  the position is preserved.
       and then (for all J in Index_Type =>
                  (if J /= I
                     and then Parent (T'Old, J) /= Empty
                     and then (Parent (T'Old, J) /= I
                               or else Position (T'Old, J) = Left)
                     and then (Parent (T'Old, Parent (T'Old, J)) /= I
                               or else Position (T'Old, Parent (T'Old, J)) = Left
                               or else Position (T'Old, J) = Right)
                   then Position (T, J) = Position (T'Old, J)))

       --  Nodes in the tree are preserved. We are using two implications
       --  instead of a Boolean equality, as automatic provers work better with
       --  two implications, which they can instantiate just for the directions
       --  of interest in a given proof.
       and then (for all J in Index_Type =>
                  (if Model (T) (J).K then Model (T'Old) (J).K))
       and then (for all J in Index_Type =>
                  (if Model (T'Old) (J).K then Model (T) (J).K))

       --  Values are preserved
       and then Values (T) = Values (T'Old)

       --  The right child of I now is the former left child of I's former right
       --  child.
       and then Peek (T, I, Right) = Peek (T'Old, Peek (T'Old, I, Right), Left)

       --  I's former right child has taken its place in the tree
       and then (if Parent (T'Old, I) /= 0 then
                      Peek (T, Parent (T'Old, I), Position (T'Old, I)) =
                      Peek (T'Old, I, Right))

       --  I is now the left child of its former right child
       and then Peek (T, Peek (T'Old, I, Right), Left) = I

       --  Other children are preserved
       and then
       (for all J in Index_Type =>
           (for all D in Direction =>
               (if (J /= I or D = Left)
                 and (J /= Parent (T'Old, I) or else D /= Position (T'Old, I))
                 and (J /= Peek (T'Old, I, Right) or else D = Right)
                 and Model (T) (J).K
                then Peek (T, J, D) = Peek (T'Old, J, D))));

   procedure Right_Rotate (T : in out Search_Tree; I : Index_Type) with
     Pre  =>
       --  The tree is not empty
       Size (T) > 0

       --  I is in the tree
       and then Model (T) (I).K

       --  I has a left child
       and then Peek (T, I, Left) /= Empty,
     Post =>
       --  The size of the tree is preserved
       Size (T) = Size (T)'Old

       --  When rotating on the root, the left child of the root becomes the
       --  new root, otherwise the root is preserved.
       and then (if Root (T)'Old /= I then Root (T) = Root (T)'Old
                 else Root (T) = Peek (T'Old, I, Left))

       --  The left child of I becomes it parent, of which I becomes the right
       --  child.
       and then Parent (T, I) = Peek (T'Old, I, Left)
       and then Position (T, I) = Right

       --  The parent of I becomes the parent of its previous left child, and
       --  unless I was root, as the same child (left or right).
       and then Parent (T, Peek (T'Old, I, Left)) = Parent (T'Old, I)
       and then (if Root (T)'Old /= I
                 then Position (T, Peek (T'Old, I, Left)) = Position (T'Old, I))

       --  During the rotation, the subtree located at the right child of the
       --  left child of I becomes the left child of I.
       and then (if Peek (T'Old, Peek (T'Old, I, Left), Right) /= Empty
                 then Parent (T, Peek (T'Old, Peek (T'Old, I, Left), Right)) = I
                   and then Position (T, Peek (T'Old, Peek (T'Old, I, Left), Right)) = Left)

       --  Except for I, its left child, and the right child of its left child,
       --  the parent link is preserved.
       and then (for all J in Index_Type =>
                  (if J /= I
                     and then (Parent (T'Old, J) /= I
                               or else Position (T'Old, J) = Right)
                     and then (Parent (T'Old, J) = Empty
                               or else Parent (T'Old, Parent (T'Old, J)) /= I
                               or else Position (T'Old, Parent (T'Old, J)) = Right
                               or else Position (T'Old, J) = Left)
                   then Parent (T, J) = Parent (T'Old, J)))

       --  Except for I, its left child, and the right child of its left child,
       --  the position is preserved.
       and then (for all J in Index_Type =>
                  (if J /= I
                     and then Parent (T'Old, J) /= Empty
                     and then (Parent (T'Old, J) /= I
                               or else Position (T'Old, J) = Right)
                     and then (Parent (T'Old, Parent (T'Old, J)) /= I
                               or else Position (T'Old, Parent (T'Old, J)) = Right
                               or else Position (T'Old, J) = Left)
                   then Position (T, J) = Position (T'Old, J)))

       --  Nodes in the tree are preserved. We are using two implications
       --  instead of a Boolean equality, as automatic provers work better with
       --  two implications, which they can instantiate just for the directions
       --  of interest in a given proof.
       and then (for all J in Index_Type =>
                  (if Model (T) (J).K then Model (T'Old) (J).K))
       and then (for all J in Index_Type =>
                  (if Model (T'Old) (J).K then Model (T) (J).K))

       --  Values are preserved
       and then Values (T) = Values (T'Old)

       --  The left child of I now is the former right child of I's former left
       --  child.
       and then Peek (T, I, Left) = Peek (T'Old, Peek (T'Old, I, Left), Right)

       --  I's former left child has taken its place in the tree
       and then (if Parent (T'Old, I) /= 0 then
                      Peek (T, Parent (T'Old, I), Position (T'Old, I)) =
                      Peek (T'Old, I, Left))

       --  I is now the right child of its former left child
       and then Peek (T, Peek (T'Old, I, Left), Right) = I

       --  Other children are preserved
       and then
       (for all J in Index_Type =>
           (for all D in Direction =>
               (if (J /= I or D = Right)
                 and (J /= Parent (T'Old, I) or else D /= Position (T'Old, I))
                 and (J /= Peek (T'Old, I, Left) or else D = Left)
                 and Model (T) (J).K
                then Peek (T, J, D) = Peek (T'Old, J, D))));

private

   type Value_Array is array (Index_Type) of Natural;

   type Search_Tree is record
      Root   : Extended_Index_Type := Empty;
      Struct : Forest;
      Values : Value_Array := (others => 0);
   end record
     with Type_Invariant =>
       (if Size (Struct) = 0 then Root = Empty
        else Root /= Empty
          and then Valid_Root (Struct, Root)
          and then Ordered_Leafs (Struct, Root, Values));

   function Ordered_Leafs (F : Forest; Root : Index_Type; Values : Value_Array)
     return Boolean
   --  Returns True iff the values in the tree rooted at Root are ordered in
   --  strictly ascending chain in a left-to-right depth-first traversal of
   --  the tree.

   with
     Ghost,
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
