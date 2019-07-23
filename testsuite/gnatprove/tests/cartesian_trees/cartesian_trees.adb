package body Cartesian_Trees with SPARK_Mode is

   --------------------------------------------
   -- Ghost local subprograms used for proof --
   --------------------------------------------

   procedure Belongs_To_Parent (T : Tree_Cell_Array; R, X : Positive) with
     Ghost,
     Global => null,
     Pre => R in T'Range and then X in T'Range
     and then Valid_Tree_Cell (T)
     and then Well_Formed (T)
     and then Belongs_To (T, R, X),
     Post => (X = R or (T (X).Parent /= 0 and then Belongs_To (T, R, T (X).Parent)));
   --  Lemma: T is a well formed tree.
   --  If X is a non-root element of the subtree rooted at R in T, then it has
   --  a non-zero parent which also belongs to the subtree rooted at R in T.

   procedure Belongs_To_Value (T : Tree_Cell_Array; S : Seq; R, X : Positive) with
     Ghost,
     Global => null,
     Pre => R in T'Range and then X in T'Range
     and then Valid_Tree_Cell (T)
     and then Well_Formed (T)
     and then (T'Length = S'Length
               and then T'First = 1
               and then Is_Heap (T, S))
     and then Belongs_To (T, R, X),
     Post => S (X) >= S (R);
   --  Lemma: T is a well formed tree with the heap property with respect to S.
   --  If X belongs to the subtree rooted at R in T, then the value of S at
   --  index X is bigger than the value at index R.

   function Min (S : Seq) return Positive with
     Ghost,
     Pre  => S'Length > 0,
     Post => Min'Result in S'Range and then (for all E of S => E >= S (Min'Result));
   --  Return the index containing the minimal element in the sequence. It is
   --  used to provide a witness for the existence of a root node.

   -----------------------
   -- Belongs_To_Parent --
   -----------------------

   procedure Belongs_To_Parent (T : Tree_Cell_Array; R, X : Positive) is
   begin

      --  The proof is done by case.
      --  Use a recursive calls to prove the property by structural induction
      --  over the tree structure.

      if X = R then
         return;
      elsif T (R).Left /= 0 and then Belongs_To (T, T (R).Left, X) then
         Belongs_To_Parent (T, T (R).Left, X);
         pragma Assert (Well_Formed (T, R));
      else
         Belongs_To_Parent (T, T (R).Right, X);
         pragma Assert (Well_Formed (T, R));
      end if;
   end Belongs_To_Parent;

   ----------------------
   -- Belongs_To_Value --
   ----------------------

   procedure Belongs_To_Value (T : Tree_Cell_Array; S : Seq; R, X : Positive) is
   begin

      --  The proof is done by case.
      --  Use a recursive calls to prove the property by structural induction
      --  over the tree structure.

      if X = R then
         return;
      elsif T (R).Left /= 0 and then Belongs_To (T, T (R).Left, X) then
         pragma Assert (Well_Formed (T, R));
         Belongs_To_Value (T, S, T (R).Left, X);
      else
         pragma Assert (Well_Formed (T, R));
         Belongs_To_Value (T, S, T (R).Right, X);
      end if;
   end Belongs_To_Value;

   --------------------
   -- Left_Neighbors --
   --------------------

   function Left_Neighbors (S : Seq) return Seq is
      subtype Small_Nat is Natural range 0 .. S'Last;
      type Small_Nat_Array is array (S'First .. S'Last) of Small_Nat;
      Stk_Content : Small_Nat_Array := (others => 0);
      Stk_Top     : Small_Nat := 0;
      Left        : Seq := (S'Range => 0);

   begin
      for I in S'Range loop
         while Stk_Top /= 0 and then S (Stk_Content (Stk_Top)) > S (I) loop
            pragma Loop_Invariant (Stk_Top <= Stk_Top'Loop_Entry);
            pragma Loop_Invariant
              (for all L in S'First .. I - 1 =>
                 (if L > Stk_Content (Stk_Top) then
                       S (L) > S (I)));
            Stk_Top := Stk_Top - 1;
         end loop;
         Left (I) := (if Stk_Top /= 0 then Stk_Content (Stk_Top) else 0);

         pragma Loop_Invariant (Stk_Top < I);
         pragma Loop_Invariant
           (for all K in 1 .. Stk_Top => Stk_Content (K) in 1 .. I - 1);

         --  Invariant for the last slice

         pragma Loop_Invariant
           (if Stk_Top = 0 then
              (for all L in S'First .. I - 1 => S (L) > S (I))
            else S (Stk_Content (Stk_Top)) <= S (I)
            and (for all L in Stk_Content (Stk_Top) + 1 .. I - 1 =>
                S (L) > S (I)));

         --  Invariant for the first slice

         pragma Loop_Invariant
           (if Stk_Top /= 0 then
              (for all L in S'First .. Stk_Content (1) - 1 =>
                   S (L) > S (Stk_Content (1))));

         --  Invariant for other slices

         pragma Loop_Invariant
           (for all K in 2 .. Stk_Top =>
              Stk_Content (K - 1) < Stk_Content (K)
            and S (Stk_Content (K - 1)) <= S (Stk_Content (K))
            and (for all L in Stk_Content (K - 1) + 1 .. Stk_Content (K) - 1 =>
                S (L) > S (Stk_Content (K))));

         --  Invariant for left

         pragma Loop_Invariant
           (for all K in 1 .. I =>
              (if Left (K) = 0 then
                   (for all L in S'First .. K - 1 => S (L) > S (K))
               else Left (K) in 1 .. K - 1
               and S (Left (K)) <= S (K)
               and (for all L in Left (K) + 1 .. K - 1 => S (L) > S (K))));
         Stk_Top := Stk_Top + 1;
         Stk_Content (Stk_Top) := I;
      end loop;

      return Left;
   end Left_Neighbors;

   ---------
   -- Min --
   ---------

   function Min (S : Seq) return Positive is
   begin
      return X : Positive := 1 do
         for I in 2 .. S'Last loop
            if S (I) < S (X) then
               X := I;
            end if;
            pragma Loop_Invariant (X in S'Range);
            pragma Loop_Invariant
              (for all K in 1 .. I => S (K) >= S (X));
         end loop;
      end return;
   end Min;

   -------------
   -- Mk_Tree --
   -------------

   function Mk_Tree (S : Seq) return Tree is
      Left  : constant Seq := Left_Neighbors (S);
      Right : constant Seq := Right_Neighbors (S);

   begin
      return T : Tree (S'Length) do
         for I in S'Range loop

            --  Properties that can be proved on each node during the
            --  construction of the tree.

            pragma Loop_Invariant (Well_Formed (T.Cells));
            pragma Loop_Invariant (Is_Heap (T.Cells, S));

            --  Definition of the root node

            pragma Loop_Invariant
              (if T.Root = 0 then
                 (for all K in 1 .. I - 1 => Right (K) /= 0 or Left (K) /= 0)
               else (T.Root in 1 .. I - 1 and then
                     (Right (T.Root) = 0 and Left (T.Root) = 0 and T.Cells (T.Root).Parent = 0)));

            --  Frame condition

            pragma Loop_Invariant
              (for all K in I .. S'Last => T.Cells (K).Parent = 0);

            --  Definition of other nodes

            pragma Loop_Invariant
              (for all K in 1 .. I - 1 =>
                 (if Right (K) = 0 and Left (K) = 0 then T.Cells (K).Parent = 0
                  elsif Left (K) = 0 or else (Right (K) > 0 and then S (Right (K)) > S (Left (K)))
                  then T.Cells (K).Parent = Right (K) and T.Cells (Right (K)).Left = K
                  else T.Cells (K).Parent = Left (K) and T.Cells (Left (K)).Right = K));

            if Right (I) = 0 and Left (I) = 0 then
               T.Root := I;
            elsif Left (I) = 0 or else
              (Right (I) > 0 and then S (Right (I)) > S (Left (I))) then

               --  To propagate the well-formed property, we need to show that
               --  we do not override another node when updating the tree.

               pragma Assert (Well_Formed (T.Cells, Right (I)));
               begin
                  pragma Assert
                    (if T.Cells (Right (I)).Left /= 0 then
                        T.Cells (T.Cells (Right (I)).Left).Parent = Right (I));
                  pragma Assert_And_Cut (T.Cells (Right (I)).Left = 0);
               end;

               T.Cells (I).Parent := Right (I);
               T.Cells (Right (I)).Left := I;

               --  Right (I) is still well-formed

               pragma Assert (I < Right (I));
               pragma Assert (I /= T.Cells (Right (I)).Parent);
               pragma Assert (Well_Formed (T.Cells, Right (I)));
            else

               --  To propagate the well-formed property, we need to show that
               --  we do not override another node when updating the tree.

               pragma Assert (Well_Formed (T.Cells, Left (I)));
               begin
                  pragma Assert
                    (Right (I) = 0 or else
                         (Left (I) > 0 and then S (Left (I)) > S (Right (I))));
                  pragma Assert
                    (if T.Cells (Left (I)).Right /= 0 then
                        T.Cells (T.Cells (Left (I)).Right).Parent = Left (I));
                  pragma Assert_And_Cut (T.Cells (Left (I)).Right = 0);
               end;

               T.Cells (I).Parent := Left (I);
               T.Cells (Left (I)).Right := I;

               --  Left (I) is still well-formed

               pragma Assert (I > Left (I));
               pragma Assert (I /= T.Cells (Left (I)).Parent);
               pragma Assert (Well_Formed (T.Cells, Left (I)));
            end if;

            --  we preserve the well-formed property

            pragma Assert (Well_Formed (T.Cells, I));
            pragma Assert (for all K in S'Range =>
                             Well_Formed (T.Cells, K));
         end loop;

         --  The tree has the heap property

         pragma Assert (Is_Heap (T.Cells, S));

         --  The tree has a (single) root

         begin
            pragma Assert (T.Cells (Min (S)).Parent = 0);
            pragma Assert (T.Cells (T.Root).Parent = 0);
            pragma Assert (for all X in T.Cells'Range =>
                             (if T.Cells (X).Parent = 0
                              then (for all Y in T.Cells'Range =>
                                        (if Y /= X then S (Y) > S (X)))));
            pragma Assert (for all X in T.Cells'Range =>
                             (if T.Cells (X).Parent = 0 and X /= T.Root then S (X) > S (T.Root)));
            pragma Assert (for all X in T.Cells'Range =>
                             (if T.Cells (X).Parent = 0 and X /= T.Root then S (X) < S (T.Root)));
            pragma Assert_And_Cut (One_Root (T));
         end;

         --  Traversing the tree using in order traversal produces the input
         --  sequence.
         --  Part 1: all nodes in the left subtree rooted at any node x in the
         --  tree are smaller than x.

         begin
            --  Show the property for every element of the tree

            for I in S'Range loop
               if T.Cells (I).Left /= 0 then

                  --  The left node itself is smaller than its parent

                  begin
                     pragma Assert (Well_Formed (T.Cells, I));
                     pragma Assert (T.Cells (T.Cells (I).Left).Parent = I);
                     pragma Assert (I = Right (T.Cells (I).Left));
                     pragma Assert_And_Cut (T.Cells (I).Left < I and S (I) < S (T.Cells (I).Left));
                  end;

                  --  Show that the other elements of the left subtree
                  --  rooted at I are also smaller than I by induction over
                  --  the value stored in the sequence at each index starting
                  --  from 0.

                  for W in Natural loop
                     for J in S'Range loop
                        if S (J) = W and Belongs_To (T.Cells, T.Cells (I).Left, J) and J /= T.Cells (I).Left then

                           --  Consider J's parent. We can apply the inductive
                           --  hypothesis recursively since its associated
                           --  value is smaller than W.

                           Belongs_To_Parent (T.Cells, T.Cells (I).Left, J);
                           pragma Assert (T.Cells (J).Parent /= 0);
                           pragma Assert (Is_Heap (T.Cells, S));
                           pragma Assert (S (T.Cells (J).Parent) < S (J));
                           pragma Assert (Belongs_To (T.Cells, T.Cells (I).Left, T.Cells (J).Parent));
                           pragma Assert (S (T.Cells (J).Parent) <= W - 1);
                           pragma Assert
                             (for all K in S'Range =>
                                (if S (K) <= W - 1 and then T.Cells (I).Left /= 0 and then Belongs_To (T.Cells, T.Cells (I).Left, K) then
                                      K < I));
                           pragma Assert (T.Cells (J).Parent < I);

                           --  Consider the case when J is at the right of
                           --  its parent.

                           if J > T.Cells (J).Parent then

                              --  Its parent is its left neighbor

                              pragma Assert (Well_Formed (T.Cells, J));
                              pragma Assert (Well_Formed (T.Cells, T.Cells (J).Parent));
                              pragma Assert (T.Cells (T.Cells (J).Parent).Right = J);
                              pragma Assert (T.Cells (T.Cells (J).Parent).Left /= J);
                              pragma Assert (T.Cells (J).Parent = Left (J));

                              --  S (I) is smaller than S (J)

                              Belongs_To_Value (T.Cells, S, T.Cells (I).Left, J);
                              pragma Assert (S (I) < S (T.Cells (I).Left));
                              pragma Assert (S (I) < S (J));

                              --  I cannot be smaller than J by definition of
                              --  left neighbors.

                              pragma Assert (if I < J then (for some L in Left (J) + 1 .. J - 1 => S (L) < S (J)));
                              pragma Assert (J < I);
                           end if;
                        end if;

                        --  We have proved the property for elements of the
                        --  left subtree of I up to range J and value W.

                        pragma Loop_Invariant
                          (for all K in 1 .. J =>
                             (if S (K) = W and then T.Cells (I).Left /= 0 and then Belongs_To (T.Cells, T.Cells (I).Left, K) then
                                   K < I));
                     end loop;
                     pragma Loop_Invariant
                       (for all K in S'Range =>
                          (if S (K) <= W and then T.Cells (I).Left /= 0 and then Belongs_To (T.Cells, T.Cells (I).Left, K) then
                                K < I));
                  end loop;
                  pragma Assert (Left_Smaller (T.Cells, I));
               end if;

               --  We have proved Left_Smaller up to range I

               pragma Assert (Left_Smaller (T.Cells, I));
               pragma Loop_Invariant
                 (for all X in 1 .. I => Left_Smaller (T.Cells, X));
            end loop;

            --  Left_Smaller is proved, forget about the proof steps

            pragma Assert_And_Cut (for all X in S'Range => Left_Smaller (T.Cells, X));
         end;

         --  Part 2: all nodes in the right subtree rooted at any node x in the
         --  tree are larger than x.

         begin

            --  Show the property for every element of the tree

            for I in S'Range loop
               if T.Cells (I).Right /= 0 then

                  --  The right node itself is larger than its parent

                  begin
                     pragma Assert (Well_Formed (T.Cells, I));
                     pragma Assert (T.Cells (T.Cells (I).Right).Parent = I);
                     pragma Assert (I = Left (T.Cells (I).Right));
                     pragma Assert_And_Cut (T.Cells (I).Right > I and S (I) < S (T.Cells (I).Right));
                  end;

                  --  Show that the other elements of the right subtree
                  --  rooted at I are also larger than I by induction over
                  --  the value stored in the sequence at each index starting
                  --  from 0.

                  for W in Natural loop
                     for J in S'Range loop
                        if S (J) = W and Belongs_To (T.Cells, T.Cells (I).Right, J) and J /= T.Cells (I).Right then

                           --  Consider J's parent. We can apply the inductive
                           --  hypothesis recursively since its associated
                           --  value is smaller than W.

                           Belongs_To_Parent (T.Cells, T.Cells (I).Right, J);
                           pragma Assert (T.Cells (J).Parent /= 0);
                           pragma Assert (Is_Heap (T.Cells, S));
                           pragma Assert (S (T.Cells (J).Parent) < S (J));
                           pragma Assert (Belongs_To (T.Cells, T.Cells (I).Right, T.Cells (J).Parent));
                           pragma Assert (S (T.Cells (J).Parent) <= W - 1);
                           pragma Assert
                             (for all K in S'Range =>
                                (if S (K) <= W - 1 and then T.Cells (I).Right /= 0 and then Belongs_To (T.Cells, T.Cells (I).Right, K) then
                                      K > I));
                           pragma Assert (T.Cells (J).Parent > I);

                           --  Consider the case when J is at the left of
                           --  its parent.

                           if J < T.Cells (J).Parent then

                              --  Its parent is its right neighbor

                              pragma Assert (Well_Formed (T.Cells, J));
                              pragma Assert (Well_Formed (T.Cells, T.Cells (J).Parent));
                              pragma Assert (T.Cells (T.Cells (J).Parent).Left = J);
                              pragma Assert (T.Cells (T.Cells (J).Parent).Right /= J);
                              pragma Assert (T.Cells (J).Parent = Right (J));

                              --  S (I) is larger than S (J)

                              Belongs_To_Value (T.Cells, S, T.Cells (I).Right, J);
                              pragma Assert (S (I) < S (T.Cells (I).Right));
                              pragma Assert (S (I) < S (J));

                              --  I cannot be larger than J by definition of
                              --  right neighbors.

                              pragma Assert (if I > J then (for some L in Right (J) + 1 .. J - 1 => S (L) > S (J)));
                              pragma Assert (J > I);
                           end if;
                        end if;

                        --  We have proved the property for elements of the
                        --  right subtree of I up to range J and value W.

                        pragma Loop_Invariant
                          (for all K in 1 .. J =>
                             (if S (K) = W and then T.Cells (I).Right /= 0 and then Belongs_To (T.Cells, T.Cells (I).Right, K) then
                                   K > I));
                     end loop;
                     pragma Loop_Invariant
                       (for all K in S'Range =>
                          (if S (K) <= W and then T.Cells (I).Right /= 0 and then Belongs_To (T.Cells, T.Cells (I).Right, K) then
                                K > I));
                  end loop;
                  pragma Assert (Right_Bigger (T.Cells, I));
               end if;

               --  We have proved Right_Bigger up to range I

               pragma Assert (Right_Bigger (T.Cells, I));
               pragma Loop_Invariant
                 (for all X in 1 .. I => Right_Bigger (T.Cells, X));
            end loop;

            --  Right_Bigger is proved, forget about the proof steps

            pragma Assert_And_Cut (for all X in S'Range => Right_Bigger (T.Cells, X));
         end;
      end return;
   end Mk_Tree;

   ---------------------
   -- Right_Neighbors --
   ---------------------

   function Right_Neighbors (S : Seq) return Seq is
      subtype Small_Nat is Natural range 0 .. S'Last;
      type Small_Nat_Array is array (S'First .. S'Last) of Small_Nat;
      Stk_Content : Small_Nat_Array := (others => 0);
      Stk_Top     : Small_Nat := 0;
      Right       : Seq := (S'Range => 0);

   begin
      for I in reverse S'Range loop
         while Stk_Top /= 0 and then S (Stk_Content (Stk_Top)) > S (I) loop
            pragma Loop_Invariant (Stk_Top <= Stk_Top'Loop_Entry);
            pragma Loop_Invariant
              (for all L in I + 1 .. S'Last =>
                 (if L < Stk_Content (Stk_Top) then
                       S (L) > S (I)));
            Stk_Top := Stk_Top - 1;
         end loop;
         Right (I) := (if Stk_Top /= 0 then Stk_Content (Stk_Top) else 0);

         pragma Loop_Invariant (Stk_Top <= S'Last - I);
         pragma Loop_Invariant
           (for all K in 1 .. Stk_Top => Stk_Content (K) in I + 1 .. S'Last);

         --  Invariant for the last slice

         pragma Loop_Invariant
           (if Stk_Top = 0 then
              (for all L in I + 1 .. S'Last => S (L) > S (I))
            else S (Stk_Content (Stk_Top)) <= S (I)
            and (for all L in I + 1 .. Stk_Content (Stk_Top) - 1 =>
                S (L) > S (I)));

         --  Invariant for the first slice

         pragma Loop_Invariant
           (if Stk_Top /= 0 then
              (for all L in Stk_Content (1) + 1 .. S'Last =>
                   S (L) > S (Stk_Content (1))));

         --  Invariant for other slices

         pragma Loop_Invariant
           (for all K in 2 .. Stk_Top =>
              Stk_Content (K - 1) > Stk_Content (K)
            and S (Stk_Content (K - 1)) <= S (Stk_Content (K))
            and (for all L in Stk_Content (K) + 1 .. Stk_Content (K - 1) - 1 =>
                S (L) > S (Stk_Content (K))));

         --  Invariant for right

         pragma Loop_Invariant
           (for all K in I .. S'Last =>
              (if Right (K) = 0 then
                   (for all L in K + 1 .. S'Last => S (L) > S (K))
               else Right (K) in K + 1 .. S'Last
               and S (Right (K)) <= S (K)
               and (for all L in K + 1 .. Right (K) - 1 => S (L) > S (K))));
         Stk_Top := Stk_Top + 1;
         Stk_Content (Stk_Top) := I;
      end loop;

      return Right;
   end Right_Neighbors;

end Cartesian_Trees;

