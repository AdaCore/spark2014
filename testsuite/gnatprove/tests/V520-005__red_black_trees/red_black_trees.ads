with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Big_Intervals; use Big_Intervals;
with Infinite_Sequences;

package Red_Black_Trees with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Red_Or_Black is (Red, Black);

   type Tree_Cell;

   type Tree is access Tree_Cell;

   type Tree_Cell is record
      Value : Integer;
      Color : Red_Or_Black;
      Left  : Tree;
      Right : Tree;
   end record;

   ------------------------------------------------
   -- Model of the tree : A sequence of integers --
   ------------------------------------------------

   function Size (X : access constant Tree_Cell) return Big_Natural is
     (if X = null then 0
      else Size (X.Left) + Size (X.Right) + 1)
   with Subprogram_Variant => (Structural => X);
   --  Number of elements in the tree

   type Model_Type is new Infinite_Sequences.Sequence with Ghost;
   --  We use our own sequences implemented as maps so that they do not always
   --  start at 1. The implementation of sequences as maps is inefficient though,
   --  so it is only OK because the models are ghost.

   function Model (X : access constant Tree_Cell; Fst : Big_Positive) return Model_Type
   with Ghost,
     Post => First (Model'Result) = Fst and then Last (Model'Result) = Fst + Size (X) - 1
     and then
       (if X /= null then
          Is_Concat (Model (X.Left, Fst),
                     X.Value,
                     Model (X.Right, Fst + Size (X.Left) + 1),
                     Model'Result)),
     Subprogram_Variant => (Decreases => Size (X));
   --  A model of a tree is an array containing the values of X in order. We
   --  first traverse the left subtree, then the root, and then the right
   --  subtree.

   function Model (X : access constant Tree_Cell) return Model_Type is
      (Model (X, 1))
   with Ghost,
     Post => First (Model'Result) = 1 and then Last (Model'Result) = Size (X);

   --------------------------
   -- Properties of Models --
   --------------------------

   function Is_Sorted (T : Model_Type) return Boolean is
      (for all I in Interval'(First (T), Last (T)) =>
         (for all J in Interval'(First (T), Last (T)) =>
              (if I < J then Get (T, I) < Get (T, J))))
   with Ghost,
     Post => True;
   --  Whether a model is sorted

   function Contains (T : Model_Type; V : Integer) return Boolean is
      (for some I in Interval'(First (T), Last (T)) => Get (T, I) = V)
   with Ghost,
     Post => True;
   --  Inclusion in a model

   function Model_Insert (T : Model_Type; V : Integer; R : Model_Type) return Boolean is
     (Contains (R, V)
      and (for all J in Interval'(First (T), Last (T)) =>
             Contains (R, Get (T, J)))
      and (for all J in Interval'(First (R), Last (R)) =>
             Get (R, J) = V or Contains (T, Get (R, J))))
   with Ghost;
   --  Whether a model R is the result of inserting V inside T

   ----------------
   --  Balancing --
   ----------------

   function Nb_Black (T : access constant Tree_Cell) return Big_Natural is
     (if T = null then 0
      elsif T.Color = Red then Nb_Black (T.Left)
      else Nb_Black (T.Left) + 1) with
     Post => Nb_Black'Result <= Size (T),
     Subprogram_Variant => (Decreases => Size (T));
   --  Number of black nodes in the left most branch of T

   function Same_Nb_Black (T : access constant Tree_Cell) return Boolean is
     (T = null
      or else (Nb_Black (T.Left) = Nb_Black (T.Right)
               and then Same_Nb_Black (T.Left)
               and then Same_Nb_Black (T.Right)))
   with Ghost,
     Subprogram_Variant => (Decreases => Size (T));
   --  All branches of T contain the same number of black nodes

   function Get_Color (T : access constant Tree_Cell) return Red_Or_Black is
     (if T = null then Black else T.Color);
   --  Color of the root of a tree. If the tree is empty, it is assimilated to
   --  a black node.

   function Scarce_Red (T : access constant Tree_Cell) return Boolean is
     (T = null
      or else
        ((if T.Color = Red then Get_Color (T.Left) = Black
          and then Get_Color (T.Right) = Black)
         and Scarce_Red (T.Left)
         and Scarce_Red (T.Right)))
   with Ghost,
     Subprogram_Variant => (Decreases => Size (T));
   --  A red node is always followed by two black nodes

   function Balanced (T : access constant Tree_Cell) return Boolean is
     (Get_Color (T) = Black
      and then Scarce_Red (T)
      and then Same_Nb_Black (T))
   with Ghost;
   --  Use colors to enforce balancing of the tree:
   --   * The root is always black
   --   * A red node can only be followed by black nodes
   --   * There are the same number of black nodes in all branches

   --------------------------
   --  Red black trees API --
   --------------------------

   function RBT_Invariant (T : access constant Tree_Cell) return Boolean is
     (Is_Sorted (Model (T)) and Balanced (T))
   with Ghost;
   --  Invariant of red black trees, they contain sorted values, and they are
   --  balanced.

   function Contains (T : access constant Tree_Cell; V : Integer) return Boolean
   with
     Pre  => RBT_Invariant (T),
     Post => Contains'Result = Contains (Model (T), V);

   procedure Insert (T : in out Tree; V : Integer) with
     Pre  => RBT_Invariant (T),
     Post => RBT_Invariant (T)
     and In_Range (Size (T), Size (T)'Old, Size (T)'Old + 1)
     and Model_Insert (Model (T)'Old, V, Model (T));

end Red_Black_Trees;
