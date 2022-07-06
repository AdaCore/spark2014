with Ada.Containers; use Ada.Containers;
with Ada.Containers.Functional_Sets;

package Binary_Search with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Tree;
   type Tree_Acc is access Tree;
   type Tree is record
      Data  : Integer;
      Left  : Tree_Acc;
      Right : Tree_Acc;
   end record;
   --  A binary tree containing integers

   function At_End
     (X : access constant Tree) return access constant Tree
   is
     (X)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   --  Pledge function, used to mark assertions as pledges for the analysis tool

   function M_Contains (T : access constant Tree; V : Integer) return Boolean is
      (if T = null then False
       else V = T.Data or else M_Contains (T.Left, V) or else M_Contains (T.Right, V))
   with  Subprogram_Variant => (Structural => T),
     Post => True,
     Ghost;
   --  Recursive contains function, used in the specification world

   function "<" (V : Integer; T : access constant Tree) return Boolean
     with  Subprogram_Variant => (Structural => T),
     Ghost,
     Post => "<"'Result =
       (for all I in Integer => (if M_Contains (T, I) then V < I))
     and "<"'Result =
       (T = null or else (V < T.Data and V < T.Left and V < T.Right));
   --  An integer value is smaller than a tree if it is smaller than all values
   --  of the tree.

   function "<" (T : access constant Tree; V : Integer) return Boolean
     with  Subprogram_Variant => (Structural => T),
     Ghost,
     Post => "<"'Result =
       (for all I in Integer => (if M_Contains (T, I) then I < V))
     and "<"'Result =
       (T = null or else (T.Data < V and T.Left < V and T.Right < V));
   --  A tree is smaller than an integer value if all values of the tree are
   --  smaller than the integer value.

   function Sorted (T : access constant Tree) return Boolean is
     (if T = null then True
      else T.Left < T.Data and then T.Data < T.Right
        and then Sorted (T.Left) and then Sorted (T.Right))
   with Subprogram_Variant => (Structural => T),
     Post => True,
     Ghost;
   --  A tree is sorted if its left subtree is smaller than its root value
   --  and its root value is smaller than its right subtree.

   function Contains (T : access constant Tree; V : Integer) return Boolean with
     Pre  => Sorted (T),
     Post => Contains'Result = M_Contains (T, V);
   --  Imperative contains function, implemented using a loop

   type Int_Option (Present : Boolean := False) is record
      case Present is
         when True  => Value : Integer;
         when False => null;
      end case;
   end record;
   --  Option type containing an Integer value

   function "<" (V : Int_Option; T : access constant Tree) return Boolean is
     (if V.Present then V.Value < T else True)
   with Ghost;

   function "<" (T : access constant Tree; V : Int_Option) return Boolean is
     (if V.Present then T < V.Value else True)
   with Ghost;

   function "<" (V : Int_Option; I : Integer) return Boolean is
     (if V.Present then V.Value < I else True)
   with Ghost;

   function "<" (I : Integer; V : Int_Option) return Boolean is
     (if V.Present then I < V.Value else True)
   with Ghost;

   package Int_Sets is new Ada.Containers.Functional_Sets (Integer);
   type Int_Set is new Int_Sets.Set;
   --  An infinite set of integers

   function All_V (T : access constant Tree) return Int_Set with
     Ghost,
     Subprogram_Variant => (Structural => T),
     Post => (for all I in Integer => M_Contains (T, i) = Contains (All_V'Result, I));
   --  Compute the set of all the values contained in the tree

   procedure Insert (T : in out Tree_Acc; V : Integer) with
     Pre  => Sorted (T),
     Post => Sorted (T) and M_Contains (T, V)
     and (for all I in Integer =>
            M_Contains (T, I) = (I = V or Contains (All_V (T)'Old, I)));
   --  Insertion in a binary tree. It is implemented in an iterative way using
   --  a local borrower.

end Binary_Search;
