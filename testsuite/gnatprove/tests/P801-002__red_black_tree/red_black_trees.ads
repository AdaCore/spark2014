with Tree_Model; use Tree_Model;
use Tree_Model.D_Seq;
with Conts; use Conts;

with Search_Trees; use Search_Trees;
with Binary_Trees; use Binary_Trees;

--  This package provides an implementation of balanced red black trees above
--  the search tree implemetation. Appart from the regular search tree, a red
--  black tree contains an array associating a color to each node. The
--  invariant states that there cannot be two red nodes in a row in any path
--  of the tree. The package is not proved yet.

package Red_Black_Trees with SPARK_Mode is
   type Rbt is private with Default_Initial_Condition => True;

   function Size (T : Rbt) return Extended_Index_Type with Ghost;

   procedure Insert (T : in out Rbt; V : Natural) with
   Pre => Size (T) < Max;
private

   type Color_Type is (Black, Red);
   type Color_Array is array (Index_Type) of Color_Type;

   type Rbt is record
      Struct : Search_Tree;
      Color  : Color_Array;
   end record
     with Type_Invariant => Invariant (Rbt);

   function Color (T : Rbt; I : Extended_Index_Type) return Color_Type is
      (if I = 0 then Black else T.Color (I));

   function Invariant (T : Rbt) return Boolean is
     (if Root (T.Struct) /= 0 then T.Color (Root (T.Struct)) = Black
      else
        (for all I in Index_Type =>
             (if Model (T.Struct) (I).K and I /= Root (T.Struct)
              and T.Color (Parent (T.Struct, I)) = Red
              then T.Color (I) = Black)))
   with Ghost;

   function Size (T : Rbt) return Extended_Index_Type is (Size (T.Struct));
end Red_Black_Trees;
