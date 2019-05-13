with Ada.Containers.Functional_Vectors;
with Ada.Containers.Functional_Sets;
use Ada.Containers;

package Tree_Model with SPARK_Mode is

   Max : constant := 100;
   --  Maximum number of nodes in a tree

   Empty : constant := 0;

   subtype Index_Type is Count_Type range 1 .. Max;
   --  Numbering for tree nodes

   subtype Extended_Index_Type is Index_Type'Base range Empty .. Max;
   --  Numbering extended with the value Empty representing the absence of node

   type Position_Type is (Left, Right, Top);
   subtype Direction is Position_Type range Left .. Right;

   subtype Positive_Count_Type is Count_Type range 1 .. Count_Type'Last;
   package D_Seq is new Ada.Containers.Functional_Vectors
     (Positive_Count_Type, Direction);
   use D_Seq;
   --  Sequence of directions modelling a path from the root of the tree to a
   --  node in the tree.

   type Path_Type is record
      A : Sequence;
      K : Boolean := False;
   end record
   with Predicate => Length (A) < Max;
   --  Type used to model the path from the root of a tree to a given node,
   --  which may or not be in the tree:
   --    - if a node is in the tree, the corresponding path will have K = True,
   --      and A will denote the path from the root to this node.
   --    - if a node is not in the tree, the corresponding path will have
   --      K = False and A will be empty.

   function Is_Concat (Q, V, P : Sequence) return Boolean is
     (Length (P) - Length (V) = Length (Q)
      and then (for all I in 1 .. Length (Q) => Get (P, I) = Get (Q, I))
      and then (for all I in 1 .. Length (V) =>
                 Get (P, I + Length (Q)) = Get (V, I))
      and then (for all I in Length (Q) + 1 .. Length (P) =>
                 Get (V, I - Length (Q)) = Get (P, I)))
   with Pre => Length (Q) <= Max;

   type Model_Type is array (Index_Type) of Path_Type;
   --  Type used to model the set of paths from the root of a tree to all nodes.
   --  This is useful to reason about reachability properties over a tree.

   function "=" (M1, M2 : Model_Type) return Boolean is
     (for all I in Index_Type => M1 (I).A = M2 (I).A and M1 (I).K = M2 (I).K);

   function Is_Add (S1 : Sequence; D : Direction; S2 : Sequence) return Boolean
   is
     (Length (S2) - 1 = Length (S1) and then S1 < S2
      and then Get (S2, Length (S2)) = D);

   procedure Preserve_Equal (S1, S2, S3, S4 : Sequence; D : Direction) with
     Ghost,
     Global => null,
     Pre  => S1 = S2
       and then Is_Add (S1, D, S3)
       and then Is_Add (S2, D, S4),
     Post => S3 = S4;

   procedure Preserve_Concat (S1, S2, S3, S4, T : Sequence; D : Direction) with
     Ghost,
     Global => null,
     Pre  => Length (T) <= Max
       and then Is_Concat (T, S1, S2)
       and then Is_Add (S1, D, S3)
       and then Is_Add (S2, D, S4),
     Post => Is_Concat (T, S3, S4);

   package V_Set is new Ada.Containers.Functional_Sets (Natural, "=");
   subtype Value_Set is V_Set.Set;
   use V_Set;

   function Is_Add (S1 : Value_Set; E : Natural; S2 : Value_Set) return Boolean
   is
     (not Contains (S1, E) and Contains (S2, E)
      and S1 <= S2 and Included_Except (S2, S1, E));

end Tree_Model;
