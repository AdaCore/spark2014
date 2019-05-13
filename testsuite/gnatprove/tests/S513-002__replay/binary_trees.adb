with Ada.Containers.Functional_Sets;

package body Binary_Trees with SPARK_Mode is

   pragma Warnings
     (Off, "postcondition does not check the outcome of calling");

   package I_Set is new Ada.Containers.Functional_Sets (Index_Type, "=");

   function All_Indexes return I_Set.Set with
   --  To ensure termination of the Model function, we need to keep track of
   --  all the indexes that have not been seen so far. This function is used to
   --  initialize this set.

     Ghost,
     Post =>
       (for all I in Index_Type => I_Set.Contains (All_Indexes'Result, I))
          and I_Set.Length (All_Indexes'Result) = Max
   is
      use I_Set;
      S : I_Set.Set;
   begin
      for I in Index_Type loop
         pragma Loop_Invariant (Length (S) = I - 1);
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 => Contains (S, J));
         pragma Loop_Invariant (for all J of S => J < I);
         S := Add (S, I);
      end loop;
      return S;
   end All_Indexes;

   --------------------
   -- Tree_Structure --
   --------------------

   function Tree_Structure (F : Forest) return Boolean is

      --  Cells that are not allocated yet have default values

     ((for all I in F.S + 1 .. Max => F.C (I) = (Empty, Empty, Empty, Top))

      --  Parent and children of all cells are allocated or empty

      and then (for all I in Index_Type => F.C (I).Parent in Empty .. F.S)
      and then (for all I in Index_Type => F.C (I).Left in Empty .. F.S)
      and then (for all I in Index_Type => F.C (I).Right in Empty .. F.S)

      --  If a cell is the root of a tree (position Top) it has no parent

      and then (for all I in Index_Type =>
                 (if F.C (I).Position = Top then F.C (I).Parent = Empty))

      --  If a cell I has a left child, then its left child has position Left
      --  and parent I.

      and then (for all I in Index_Type =>
                 (if F.C (I).Left /= Empty then
                    F.C (F.C (I).Left).Position = Left
                    and then F.C (F.C (I).Left).Parent = I))

      --  If a cell I has a right child, then its right child has position Right
      --  and parent I.

      and then (for all I in Index_Type =>
                 (if F.C (I).Right /= Empty then
                   F.C (F.C (I).Right).Position = Right
                   and then F.C (F.C (I).Right).Parent = I))

      --  If a cell is a child (position Left or Right), then it is the child
      --  of its parent.

      and then (for all I in Index_Type =>
                 (if F.C (I).Parent /= Empty and then F.C (I).Position = Left
                  then F.C (F.C (I).Parent).Left = I))
      and then (for all I in Index_Type =>
                 (if F.C (I).Parent /= Empty and then F.C (I).Position = Right
                  then F.C (F.C (I).Parent).Right = I)));

   function Size (F : Forest) return Extended_Index_Type is (F.S);

end Binary_Trees;
