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

   function Pledge
     (Dummy    : access constant Tree;
      Property : Boolean) return Boolean
   is
     (Property)
   with Ghost,
     Annotate => (GNATProve, Pledge);
   --  Pledge function, used to mark assertions as pledges for the analysis tool

   function M_Contains (T : access constant Tree; V : Integer) return Boolean is
      (if T = null then False
       else V = T.Data or else M_Contains (T.Left, V) or else M_Contains (T.Right, V))
   with Annotate => (GNATprove, Terminating),
     Ghost;
   --  Recursive contains function, used in the specification world

   pragma Annotate
     (GNATprove, False_Positive, """M_Contains"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   function "<" (V : Integer; T : access constant Tree) return Boolean
     with Annotate => (GNATprove, Terminating),
     Ghost,
     Post => "<"'Result =
       (for all I in Integer => (if M_Contains (T, I) then V < I))
     and "<"'Result =
       (T = null or else (V < T.Data and V < T.Left and V < T.Right));
   --  An integer value is smaller than a tree if it is smaller than all values
   --  of the tree.

   pragma Annotate
     (GNATprove, False_Positive, """<"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   function "<" (T : access constant Tree; V : Integer) return Boolean
     with Annotate => (GNATprove, Terminating),
     Ghost,
     Post => "<"'Result =
       (for all I in Integer => (if M_Contains (T, I) then I < V))
     and "<"'Result =
       (T = null or else (T.Data < V and T.Left < V and T.Right < V));
   --  A tree is smaller than an integer value if all values of the tree are
   --  smaller than the integer value.

   pragma Annotate
     (GNATprove, False_Positive, """<"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   function Sorted (T : access constant Tree) return Boolean is
     (if T = null then True
      else T.Left < T.Data and then T.Data < T.Right
        and then Sorted (T.Left) and then Sorted (T.Right))
   with Annotate => (GNATprove, Terminating),
     Ghost;
   --  A tree is sorted if its left subtree is smaller than its root value
   --  and its root value is smaller than its right subtree.

   pragma Annotate
     (GNATprove, False_Positive, """Sorted"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

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
   --  A set of integer. There are no infinite sets in Ada, this set is bounded
   --  by the size of Natural.

   function Size (T : access constant Tree) return Natural is
     (if T = null then 0
      elsif Size (T.Left) < Natural'Last - Size (T.Right)
      then Size (T.Left) + Size (T.Right) + 1
      else Natural'Last)
   with Annotate => (GNATprove, Terminating),
     Ghost;
   --  Function returning the number of elements in a tree. It is used to
   --  bound the size of the tree so that its elements can all be contained in
   --  an Int_Set. Size saturates and returns Natural'Last when more than
   --  Natural'Last elements are contained in the tree.

   pragma Annotate
     (GNATprove, False_Positive, """Size"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   function All_V (T : access constant Tree) return Int_Set with
     Ghost,
     Annotate => (GNATprove, Terminating),
     Pre  => Size (T) < Natural'Last,
     Post => Length (All_V'Result) <= Count_Type (Size (T))
     and then (for all I in Integer => M_Contains (T, i) = Contains (All_V'Result, I));
   --  Compute the set of all the values contained in the tree. It can only be
   --  used on trees with less than Natural'Last elements to not exceed the
   --  capacity of the set.

   pragma Annotate
     (GNATprove, False_Positive, """All_V"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   procedure Insert (T : in out Tree_Acc; V : Integer) with
     Pre  => Sorted (T) and Size (T) < Natural'Last,
     Post => Sorted (T) and M_Contains (T, V)
     and (for all I in Integer =>
            M_Contains (T, I) = (I = V or Contains (All_V (T)'Old, I)));
   --  Insertion in a binary tree. It is implemented in an iterative way using
   --  a local borrower.

end Binary_Search;
