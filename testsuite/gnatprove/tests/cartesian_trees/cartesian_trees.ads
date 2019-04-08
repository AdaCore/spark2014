package Cartesian_Trees with SPARK_Mode is
   subtype Small_Pos is Positive range 1 .. Positive'Last - 1;
   type Nat_Array is array (Small_Pos range <>) of Natural;
   subtype Seq is Nat_Array with
     Predicate => Seq'First = 1;

   function Left_Neighbors (S : Seq) return Seq with
     Pre  => S'Length > 0,
     Post => S'Length = Left_Neighbors'Result'Length
     and then
       (for all K in Left_Neighbors'Result'Range =>
          (if Left_Neighbors'Result (K) = 0 then
               (for all L in S'First .. K - 1 => S (L) > S (K))
           else Left_Neighbors'Result (K) in 1 .. K - 1
             and S (Left_Neighbors'Result (K)) <= S (K)
             and (for all L in Left_Neighbors'Result (K) + 1 .. K - 1 =>
                    S (L) > S (K))));
   --  Construct the sequence of all the nearest smaller values to the left
   --  of the elements of S.

   function Right_Neighbors (S : Seq) return Seq with
     Pre  => S'Length > 0,
     Post => S'Length = Right_Neighbors'Result'Length
     and then
       (for all K in Right_Neighbors'Result'Range =>
          (if Right_Neighbors'Result (K) = 0 then
               (for all L in K + 1 .. S'Last => S (L) > S (K))
           else Right_Neighbors'Result (K) in K + 1 .. S'Last
             and S (Right_Neighbors'Result (K)) <= S (K)
             and (for all L in K + 1 .. Right_Neighbors'Result (K) - 1 =>
                    S (L) > S (K))));
   --  Construct the sequence of all the nearest smaller values to the right
   --  of the elements of S.

   type Tree_Cell is record
      Left, Right, Parent : Natural;
   end record;
   type Tree_Cell_Array is array (Small_Pos range <>) of Tree_Cell;

   function Valid_Tree_Cell (T : Tree_Cell_Array) return Boolean is
       ((for all X in T'Range => T (X).Left = 0 or T (X).Left in T'Range)
       and
         (for all X in T'Range => T (X).Right = 0 or T (X).Right in T'Range)
         and
           (for all X in T'Range => T (X).Parent = 0 or T (X).Parent in T'Range));
   --  Parent, Left, and Right should either be 0 (for null) or refer to an
   --  element of the array.

   type Tree (Size : Natural) is record
      Root  : Natural := 0;
      Cells : Tree_Cell_Array (1 .. Size) := (1 .. Size => (others => 0));
   end record with
     Predicate => Valid_Tree_Cell (Cells) and (Root = 0 or Root in 1 .. Size);

   function One_Root (T : Tree) return Boolean is
     (T.Root /= 0
      and then T.Cells (T.Root).Parent = 0
      and then (for all X in T.Cells'Range =>
        (if X /= T.Root then T.Cells (X).Parent /= 0)));
   --  T.Root is a root in T and T has no other roots

   function Well_Formed (T : Tree_Cell_Array; X : Positive) return Boolean is
     ((if T (X).Left /= 0 then T (X).Left < X and T (T (X).Left).Parent = X)
      and then (if T (X).Right /= 0 then X < T (X).Right and T (T (X).Right).Parent = X)
      and then (if T (X).Parent /= 0 then
                  (if X < T (X).Parent then T (T (X).Parent).Left = X
                   else T (T (X).Parent).Right = X)))
     with Pre => X in T'Range and Valid_Tree_Cell (T);
   --  Parent, Left, and Right have the expected properties

   function Well_Formed (T : Tree_Cell_Array) return Boolean is
     (for all X in T'Range => Well_Formed (T, X))
     with Pre => Valid_Tree_Cell (T);

   function Is_Heap (T : Tree_Cell_Array; S : Seq) return Boolean is
     (for all X in T'Range =>
        (if T (X).Parent /= 0 then
             S (T (X).Parent) < S (X)))
     with Pre => T'Length = S'Length and T'First = 1 and Valid_Tree_Cell (T);
   --  T has the heap properties with respects to values of S

   function Belongs_To (T : Tree_Cell_Array; R, X : Positive) return Boolean is
     (R = X or (T (R).Left /= 0 and then Belongs_To (T, T (R).Left, X))
      or (T (R).Right /= 0 and then Belongs_To (T, T (R).Right, X)))
     with Pre  => R in T'Range and then X in T'Range and then Valid_Tree_Cell (T);
   pragma Annotate (GNATprove, Terminating, Belongs_To);
   --  Returns True is X belongs to the subtree rooted at R in T

   function Left_Smaller (T : Tree_Cell_Array; R : Positive) return Boolean is
     (for all X in T'Range =>
        (if T (R).Left /= 0 and then Belongs_To (T, T (R).Left, X) then X < R))
     with Pre => R in T'Range and then Valid_Tree_Cell (T);
   --  The left subtree of R in T contains values smaller than R

   function Left_Smaller (T : Tree_Cell_Array) return Boolean is
     (for all R in T'Range => Left_Smaller (T, R))
     with Pre => Valid_Tree_Cell (T);
   --  For every index R in T, the left subtree of R in T contains values
   --  smaller than R.

   function Right_Bigger (T : Tree_Cell_Array; R : Positive) return Boolean is
     (for all X in T'Range =>
        (if T (R).Right /= 0 and then Belongs_To (T, T (R).Right, X) then X > R))
     with Pre => R in T'Range and then Valid_Tree_Cell (T);
   --  The right subtree of R in T contains values larger than R

   function Right_Bigger (T : Tree_Cell_Array) return Boolean is
     (for all R in T'Range => Right_Bigger (T, R))
     with Pre => Valid_Tree_Cell (T);
   --  For every index R in T, the right subtree of R in T contains values
   --  larger than R.

   function Mk_Tree (S : Seq) return Tree with
   --  Construct the Cartesian tree from the sequence S and show that it has
   --  the expected properties.

     Pre => S'Length > 0 and then
     (for all X in S'Range => (for all Y in S'Range => (if S (X) = S (Y) then X = Y))),
     Post =>

     --  The result of Mk_Tree is a single, well-formed tree containing all
     --  values of S.

       Mk_Tree'Result.Size = S'Length
     and One_Root (Mk_Tree'Result)
     and Well_Formed (Mk_Tree'Result.Cells)

     --  The result of Mk_Tree has the heap property with respect to S

     and Is_Heap (Mk_Tree'Result.Cells, S)

     --  The in-order traversal of the result of Mk_Tree processes the elements
     --  of S in the right order.

     and Left_Smaller (Mk_Tree'Result.Cells) and Right_Bigger (Mk_Tree'Result.Cells);

end Cartesian_Trees;


