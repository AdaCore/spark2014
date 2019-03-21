with Tree_Model; use Tree_Model;
use Tree_Model.D_Seq;
use Tree_Model.V_Set;
with Ada.Containers; use Ada.Containers;

with Search_Trees; use Search_Trees;
with Binary_Trees; use Binary_Trees;

--  This package provides an implementation of balanced red-black trees above
--  the search tree implementation. Apart from the regular search tree, a
--  red-black tree contains an array associating a color to each node.
--  Balancing is enforced by verifying that Red nodes are properly interleaved
--  with black nodes and that the number of black nodes is the same in every
--  branch of the tree.

package Red_Black_Trees with SPARK_Mode is
   type Rbt is private with Default_Initial_Condition => True;

   function Size (T : Rbt) return Extended_Index_Type with Ghost;

   function Values (T : Rbt) return Value_Set with Ghost,
     Post => (if Size (T) = 0 then Is_Empty (Values'Result));

   function Contains (T : Rbt; V : Natural) return Boolean with
     Post => Contains'Result = Contains (Values (T), V);

   procedure Insert (T : in out Rbt; V : Natural) with
     Pre  => Size (T) < Max,
     Post => (if Contains (T'Old, V) then Values (T) = Values (T'Old)
              else Is_Add (Values (T'Old), V, Values (T)));
private

   type Color_Type is (Black, Red);
   type Color_Array is array (Index_Type) of Color_Type;

   type Rbt is record
      Struct : Search_Tree;
      Color  : Color_Array := (others => Black);
   end record
     with Type_Invariant => Invariant (Rbt);

   function Color (T : Rbt; I : Extended_Index_Type) return Color_Type is
      (if I = Empty then Black else T.Color (I));

   function Same_Nb_Blacks (T : Rbt) return Boolean with Ghost;

   function Invariant (T : Rbt) return Boolean is
     ((for all I in Index_Type =>
        (if Parent (T.Struct, I) = Empty
           or else T.Color (Parent (T.Struct, I)) = Red
         then T.Color (I) = Black))
       and Same_Nb_Blacks (T))
   with Ghost;

   function Size (T : Rbt) return Extended_Index_Type is (Size (T.Struct));

   function Values (T : Rbt) return Value_Set is (Values (T.Struct));

   function Contains (T : Rbt; V : Natural) return Boolean is
     (Contains (T.Struct, V));

end Red_Black_Trees;
