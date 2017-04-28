with Tree_Model; use Tree_Model;
use Tree_Model.D_Seq;
with Ada.Containers; use Ada.Containers;

--  This packages provides a SPARK implementation of binary trees. Since SPARK
--  forbids the use of pointers, trees are modeled using indexes inside an
--  array. The array is not global, as it would require referring to a global
--  structure in the tree type invariant which is not allowed in SPARK. To avoid
--  multiple copies, related trees are stored together forming a forest.

package Binary_Trees with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Forest is private with Default_Initial_Condition => Size (Forest) = 0;
   --  Containsory region shaped as a set of related binary trees

   function Size (F : Forest) return Extended_Index_Type;
   --  Number of allocated nodes in the forest

   function Valid_Root (F : Forest; I : Index_Type) return Boolean with
     Post => (if I > Size (F) then not Valid_Root'Result);
   --  Return True if I is a root of a binary tree in F

   function Parent (F : Forest; I : Index_Type) return Extended_Index_Type with
     Post => (if Valid_Root (F, I) then Parent'Result = Empty)
       and then (if Size (F) = 0 then Parent'Result = Empty);
   --  Parent in the corresponding binary tree

   function Position (F : Forest; I : Index_Type) return Direction with
     Pre => Parent (F, I) /= Empty;
   --  Position (Left or Right) in the corresponding binary tree

   function Peek (F : Forest; I : Index_Type; D : Direction) return Extended_Index_Type with
     Post => (if Peek'Result /= Empty then
                Position (F, Peek'Result) = D
                and then Parent (F, Peek'Result) = I
              else
                (for all J in Index_Type =>
                  (if Parent (F, J) = I then Position (F, J) /= D)))
       and then (for all J in Index_Type =>
                  (if Parent (F, J) = I and then Position (F, J) = D
                   then Peek'Result = J));
   --  Left or right child in the corresponding binary tree

   function Model (F : Forest; Root : Index_Type) return Model_Type with
   --  The model of a tree in the forest is an array representing the path
   --  from the root leading to each node in the binary tree if any. We could
   --  have made a function returning each path separately, but this function
   --  would have been recursive, leading to unproved VC when it is called in
   --  annotations (that is, nearly always).

     Ghost,
     Pre  => Valid_Root (F, Root),
     Post =>
       --  The root is part of the tree
       Model'Result (Root).K

       --  The path from the root to itself is empty
       and then Length (Model'Result (Root).A) = 0

       --  Non-root nodes are in the tree iff their parent is in the tree
       and then (for all I in Index_Type =>
                  (if I /= Root then
                    (if Parent (F, I) /= Empty
                       and then Model'Result (Parent (F, I)).K
                     then Model'Result (I).K
                     else not Model'Result (I).K)))

       --  The path from the root to non-root tree nodes is equal to the path to
       --  their parent extended by the last direction to get to the node. For
       --  other nodes, the path is empty.
       and then (for all I in Index_Type =>
                  (if Model'Result (I).K and then I /= Root
                   then Is_Add (Model'Result (Parent (F, I)).A,
                                Position (F, I),
                                Model'Result (I).A)
                   else Length (Model'Result (I).A) = 0))

       --  Nodes in the tree all have different associated paths
       and then (for all I in Index_Type =>
                  (if Model'Result (I).K then
                    (for all J in Index_Type =>
                      (if Model'Result (J).K
                         and then Model'Result (I).A = Model'Result (J).A
                       then J = I))));

   procedure Prove_Model_Total (F : Forest; Root, I : Index_Type; D : Direction) with
   --  Ghost function performing an induction to show that, if Peek returns
   --  Empty on I and D, then every path in the forest from Root through I
   --  cannot be in direction D.

     Ghost,
     Global => null,
     Pre  => Valid_Root (F, Root)

       --  I is a node in the tree rooted at Root
       and then Model (F, Root) (I).K

       --  There is no child in direction D at node I
       and then Peek (F, I, D) = Empty,

     --  Use ordering of paths to express that I is on the path from Root to J,
     --  and check that in such a case the direction taken at I is not D.
     Post => (for all J in Index_Type =>
               (if Model (F, Root) (J).K
                  and then (Model (F, Root) (I).A < Model (F, Root) (J).A)
                then Get (Model (F, Root) (J).A, Length (Model (F, Root) (I).A) + 1) /= D));

   procedure Prove_Model_Distinct (F : Forest; T1, T2 : Index_Type) with
   --  Ghost function performing an induction to show that trees rooted at
   --  different indexes in the forest are disjoint.

     Ghost,
     Global => null,
     Pre  => T1 /= T2
       and then Valid_Root (F, T1)
       and then Valid_Root (F, T2),
     Post => (for all I in Index_Type =>
               (not Model (F, T1) (I).K or not Model (F, T2) (I).K));

   procedure Extract (F       : in out Forest;
                      Root, I : Index_Type;
                      D       : Direction;
                      V       : out Extended_Index_Type)
   --  Extract the subtree starting at position D after I in the tree rooted at
   --  root in a separate tree. Store its root into V.

   with
     Pre  =>
       --  Root is the root of a tree
       Valid_Root (F, Root)

       --  I is a node in this tree
       and then Model (F, Root) (I).K,
     Post =>
       --  The size of the forest does not change
       Size (F) = Size (F)'Old

       --  Root is still the root of a tree
       and then Valid_Root (F, Root)

       --  V was the child D of I, which is now Empty
       and then V = Peek (F, I, D)'Old
       and then Peek (F, I, D) = Empty

       --  Except for V, the value of parent link is preserved
       and then (for all J in Index_Type =>
                  (if J /= V
                   then Parent (F, J) = Parent (F'Old, J)))

       --  Except for V, the value of position is preserved for nodes which have
       --  a parent.
       and then (for all J in Index_Type =>
                  (if J /= V and Parent (F, J) /= Empty
                   then Position (F, J) = Position (F'Old, J)))

       --  Except at I for child D, all other children are preserved
       and then (for all J in Index_Type =>
                  (for all E in Direction =>
                    (if J /= I or else E /= D
                     then Peek (F, J, E) = Peek (F'Old, J, E))))

       --  Except for I and V (which was not a root node anyway), all root nodes
       --  are preserved.
       and then (for all T in Index_Type =>
                  (if Valid_Root (F'Old, T) and then I /= T and then V /= T
                   then Valid_Root (F, T)))

       --  All other trees in the forest are preserved
       and then (for all T in Index_Type =>
                  (if Valid_Root (F'Old, T) and then Root /= T and then V /= T
                   then Model (F, T) = Model (F'Old, T)))

       --  V is either Empty or a new root
       and then (if V /= Empty then Valid_Root (F, V))

       --  Nodes previously in the tree rooted at Root either remain nodes in
       --  the tree rooted at Root, or for those nodes which have V on their
       --  path, become nodes in the tree rooted at V.
       and then (for all I in Index_Type =>
                  (if Model (F, Root)'Old (I).K
                   then (if V /= Empty
                           and then Model (F, Root)'Old (V).A <= Model (F, Root)'Old (I).A
                         then Model (F, V) (I).K
                         else Model (F, Root) (I).K)))

       --  Nodes in the tree rooted at Root were previously in the tree rooted
       --  at Root.
       and then (for all I in Index_Type =>
                  (if Model (F, Root) (I).K then Model (F, Root)'Old (I).K))

       --  Nodes in the tree rooted at V were previously in the tree rooted at
       --  Root.
       and then (for all I in Index_Type =>
                  (if V /= Empty and then Model (F, V) (I).K then Model (F, Root)'Old (I).K))

       --  Paths are preserved for nodes in the tree rooted at Root
       and then (for all I in Index_Type =>
                  (if Model (F, Root) (I).K then Model (F, Root) (I).A = Model (F, Root)'Old (I).A))

       --  The path for nodes in the tree rooted at V is obtained by subtracting
       --  the path from Root to V from the path from Root to the node.
       and then (for all I in Index_Type =>
                  (if V /= Empty and then Model (F, V) (I).K
                   then Is_Concat (Q => Model (F, Root)'Old (V).A,
                                   V => Model (F, V) (I).A,
                                   P => Model (F, Root)'Old (I).A)));

   procedure Plug (F       : in out Forest;
                   Root, I : Index_Type;
                   D       : Direction;
                   V       : Extended_Index_Type)
   --  Plug the tree rooted at V in F into the tree rooted at Root as a subtree
   --  starting at position D after I.

   with
     Pre =>
       --  Root is the root of a tree
       Valid_Root (F, Root)

       --  I is a node in this tree
       and then Model (F, Root) (I).K

       --  I has no child for direction D
       and then Peek (F, I, D) = Empty

       --  Root and V are different nodes
       and then Root /= V

       --  V is either empty or the root of a tree
       and then (if V /= Empty then Valid_Root (F, V)),
     Post =>
       --  The size of the forest does not change
       Size (F) = Size (F'Old)

       --  V is inserted in the tree as child D of I
       and then V = Peek (F, I, D)

       --  Except for V, roots are preserved
       and then (for all J in Index_Type =>
                  (if Valid_Root (F'Old, J) and then J /= V then Valid_Root (F, J)))
       and then (for all J in Index_Type =>
                  (if Valid_Root (F, J) then Valid_Root (F'Old, J)))

       --  Except for V, the value of parent link is preserved
       and then (for all J in Index_Type =>
                  (if J /= V
                   then Parent (F, J) = Parent (F'Old, J)))

       --  Except for V, the value of position is preserved for nodes which have
       --  a parent.
       and then (for all J in Index_Type =>
                  (if J /= V and Parent (F, J) /= Empty
                   then Position (F, J) = Position (F'Old, J)))

       --  Except at I for child D, all other children are preserved
       and then (for all J in Index_Type =>
                  (for all E in Direction =>
                    (if J /= I or else E /= D
                     then Peek (F, J, E) = Peek (F'Old, J, E))))

       --  Nodes previously in the tree rooted at Root are still in the tree
       --  rooted at Root.
       and then (for all J in Index_Type =>
                  (if Model (F, Root)'Old (J).K then Model (F, Root) (J).K))

       --  Nodes previously in the tree rooted at V are now in the tree rooted
       --  at Root.
       and then (for all J in Index_Type =>
                  (if V /= Empty and then Model (F'Old, V) (J).K
                   then Model (F, Root) (J).K))

       --  Nodes in the tree rooted at Root come either from the tree previously
       --  rooted at Root, or for those nodes which have V on their path, from
       --  the tree previously rooted at V.
       and then (for all I in Index_Type =>
                  (if Model (F, Root) (I).K
                   then (if V /= Empty and then Model (F, Root) (V).A <= Model (F, Root) (I).A
                         then Model (F'Old, V) (I).K
                         else Model (F'Old, Root) (I).K)))

       --  Paths are preserved for nodes that were previously in the tree
       and then (for all J in Index_Type =>
                  (if Model (F'Old, Root) (J).K
                   then Model (F, Root) (J).A = Model (F'Old, Root) (J).A))

       --  The path for nodes in the tree previously rooted at V is obtained
       --  by concatenating the path from Root to V and the path from V to the
       --  node.
       and then (for all J in Index_Type =>
                  (if V /= Empty and then Model (F'Old, V) (J).K
                   then Is_Concat (Q => Model (F, Root) (Peek (F, I, D)).A,  --  ??? Why Peek(F,I,D) instead of V
                                   V => Model (F'Old, V) (J).A,
                                   P => Model (F, Root) (J).A)))

       --  All other trees in the forest are preserved
       and then (for all T in Index_Type =>
                  (if Valid_Root (F'Old, T) and then Root /= T and then V /= T
                   then Model (F, T) = Model (F'Old, T)));

   procedure Insert (F       : in out Forest;
                     Root, I : Index_Type;
                     D       : Direction;
                     V       : out Index_Type)
   --  Insert a new node in F into the tree rooted at Root at position D after
   --  node I.

   with
     Pre =>
       --  Root is the root of a tree
       Valid_Root (F, Root)

       --  I is a node in this tree
       and then Model (F, Root) (I).K

       --  I has no child for direction D
       and then Peek (F, I, D) = Empty

       --  There are free nodes to use
       and then Size (F) < Max,
     Post =>
       --  The size of the forest has increased by 1
       Size (F) = Size (F)'Old + 1

       --  I is still in the tree rooted at Root
       and then Model (F, Root) (I).K

       --  V is inserted in the tree as child D of I
       and then Peek (F, I, D) = V

       --  Roots are preserved
       and then (for all I in Index_Type =>
                  (if Valid_Root (F'Old, I) then Valid_Root (F, I)
                   else not Valid_Root (F, I)))

       --  V is a new node in the tree
       and then Model (F, Root) (V).K
       and then not Model (F, Root)'Old (V).K

       --  Except for V, the value of parent link is preserved
       and then (for all J in Index_Type =>
                  (if J /= V
                   then Parent (F, J) = Parent (F'Old, J)))

       --  Except for V, the value of position is preserved for nodes which have
       --  a parent.
       and then (for all J in Index_Type =>
                  (if J /= V and Parent (F'Old, J) /= Empty
                   then Position (F, J) = Position (F'Old, J)))

       --  Except at I for child D, all other children are preserved
       and then (for all J in Index_Type =>
                  (for all E in Direction =>
                    (if J /= I or else E /= D
                     then Peek (F, J, E) = Peek (F'Old, J, E))))

       --  Nodes that are in the tree consist in nodes previously in the tree
       --  plus the new node V.
       and then (for all J in Index_Type =>
                  (if Model (F, Root) (J).K
                   then Model (F, Root)'Old (J).K or J = V))

       --  Nodes previously in the tree are still in the tree
       and then (for all J in Index_Type =>
                  (if Model (F, Root)'Old (J).K then Model (F, Root) (J).K))

       --  Paths are preserved for nodes that were previously in the tree
       and then (for all J in Index_Type =>
                  (if Model (F, Root) (J).K and J /= V
                   then Model (F, Root) (J).A = Model (F, Root)'Old (J).A))

       --  The path for node V is obtained by extending the path for node I
       and then Is_Add (Model (F, Root) (I).A, D, Model (F, Root) (V).A)

       --  All other trees in the forest are preserved
       and then (for all I in Index_Type =>
                  (if I /= Root and Valid_Root (F'Old, I)
                   then Model (F, I) = Model (F'Old, I)));

   procedure Init (F : in out Forest; Root : out Index_Type) with
   --  Insert a new node in F as a separate tree

     Pre  => Size (F) < Max,
     Post => Size (F) = Size (F)'Old + 1

       --  Root is a new root in F
       and then not Valid_Root (F'Old, Root)
       and then Valid_Root (F, Root)

       --  Value of the parent link is preserved
       and then (for all I in Index_Type => Parent (F, I) = Parent (F'Old, I))

       --  Value of position is preserved for nodes which have a parent
       and then (for all I in Index_Type =>
                  (if Parent (F, I) /= Empty then Position (F, I) = Position (F'Old, I)))

       --  Roots are preserved, except for Root which is a new root
       and then (for all I in Index_Type =>
                  (if Valid_Root (F'Old, I) then Valid_Root (F, I)))
       and then (for all I in Index_Type =>
                  (if Valid_Root (F, I) and I /= Root then Valid_Root (F'Old, I)))

       --  For all other roots, the corresponding tree is preserved
       and then (for all I in Index_Type =>
                  (if Valid_Root (F'Old, I) then Model (F, I) = Model (F'Old, I)))

       --  The only node in the tree rooted at Root is Root itself
       and then (for all I in Index_Type =>
                  (if I /= Root then not Model (F, Root) (I).K));
private

   type Cell is record
      Left, Right, Parent : Extended_Index_Type := Empty;
      Position            : Position_Type := Top;
   end record;
   type Cell_Array is array (Index_Type) of Cell;

   type Forest is record
      S : Extended_Index_Type := Empty;
      C : Cell_Array;
   end record
     with Type_Invariant => Tree_Structure (Forest);
   --  Component S gives the size of the forest. Only the cells up to index S
   --  belong to the forest. Cells after index S are free.

   function Tree_Structure (F : Forest) return Boolean with
     Global => null;
   --  Invariant of the structure of the forest

end Binary_Trees;
