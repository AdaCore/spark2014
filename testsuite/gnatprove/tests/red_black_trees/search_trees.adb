with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

package body Search_Trees with SPARK_Mode is

   ------------
   -- Values --
   ------------

   function Values (T : Search_Tree) return Value_Set with
     Refined_Post =>
       (if Size (T.Struct) = 0 then Is_Empty (Values'Result)
        else
          ((for all I in Index_Type =>
             (if Model (T.Struct, T.Root) (I).K then Contains (Values'Result, T.Values (I))))
           and then
             (for all V in Natural =>
                  (if Contains (Values'Result, V) then
                     (for some I in Index_Type =>
                            Model (T.Struct, T.Root) (I).K and then T.Values (I) = V)))))
   is
      S : Value_Set;
   begin
      if T.Root = Empty then
         return S;
      end if;

      for J in Index_Type loop
         if Model (T.Struct, T.Root) (J).K
           and then not Contains (S, T.Values (J))
         then
            S := Add (S, T.Values (J));
         end if;
         pragma Loop_Invariant (Length (S) <= To_Big_Integer (Integer (J)));
         pragma Loop_Invariant
           (for all I in 1 .. J =>
              (if Model (T.Struct, T.Root) (I).K then Contains (S, T.Values (I))));
         pragma Loop_Invariant
           (for all V in Natural =>
              (if Contains (S, V) then
                   (for some I in Index_Type =>
                        Model (T.Struct, T.Root) (I).K and then T.Values (I) = V)));
      end loop;
      return S;
   end Values;

   --------------------
   -- Ordered_Prefix --
   --------------------

   --  If Model (I).A is a prefix of Model (J).A, their values are ordered as expected

   function Ordered_Prefix (Model : Model_Type; Values : Value_Array; I, J : Index_Type) return Boolean is
     (if Get (Model (J).A, Length (Model (I).A) + 1) = Left
      then Values (J) < Values (I)
      else Values (J) > Values (I))
   with Pre => Model (I).K and then Model (J).K and then Model (I).A < Model (J).A,
     Post => Ordered_Prefix'Result in Boolean;

   -------------------
   -- Ordered_Leafs --
   -------------------

   function Ordered_Leafs (F : Forest; Root : Index_Type; Values : Value_Array) return Boolean is
     (for all I in Index_Type =>
       (for all J in Index_Type =>
         (if Model (F, Root) (I).K
            and then Model (F, Root) (J).K
            and then Model (F, Root) (I).A < Model (F, Root) (J).A
          then Ordered_Prefix (Model (F, Root), Values, I, J))));

   -------------------
   -- Correct_Place --
   -------------------

   --  The tree rooted at V in F can be inserted as path A in the tree rooted at Root in F

   function All_Less_Than (F : Forest; Root : Index_Type; Values : Value_Array; V : Natural) return Boolean is
     (for all J in Index_Type =>
        (if Model (F, Root) (J).K then Values (J) < V))
   with Ghost, Pre => Valid_Root (F, Root);
   function All_More_Than (F : Forest; Root : Index_Type; Values : Value_Array; V : Natural) return Boolean is
     (for all J in Index_Type =>
        (if Model (F, Root) (J).K then Values (J) > V))
   with Ghost, Pre => Valid_Root (F, Root);

   function Correct_Place (F : Forest; A : Sequence; Root, V : Index_Type; Values : Value_Array) return Boolean is
     (Valid_Root (F, Root) and then Valid_Root (F, V)
      and then (for all I in Index_Type =>
                    (if Model (F, Root) (I).K and Model (F, Root) (I).A < A
                     then
                       (if Get (A, Length (Model (F, Root) (I).A) + 1) = Left
                        then All_Less_Than (F, V, Values, Values (I))
                        else All_More_Than (F, V, Values, Values (I))))))
   with Ghost;

   ---------------
   -- Find_Root --
   ---------------

   --  Auxiliary ghost function used in Prove_Order_Total to retrieve the common
   --  ancestor to nodes I and J in a tree rooted at Root.

   function Find_Root (F : Forest; Root, I, J : Index_Type) return Index_Type with
     Ghost,
     Pre  =>
       --  Root is the root of a tree
       Valid_Root (F, Root)

       --  I is in this tree
       and then Model (F, Root) (I).K

       --  J is in this tree
       and then Model (F, Root) (J).K,
     Post =>
       --  The node returned is in the tree
       Model (F, Root) (Find_Root'Result).K

       --  The node returned is on the path of I
       and then Model (F, Root) (Find_Root'Result).A <= Model (F, Root) (I).A

       --  The node returned is on the path of J
       and then Model (F, Root) (Find_Root'Result).A <= Model (F, Root) (J).A

       --  The common ancestor of I and J is either I, or J, or an ancestor node
       --  such that the paths of I and J diverge at this point.
       and then (I = Find_Root'Result
                   or else J = Find_Root'Result
                   or else Get (Model (F, Root) (I).A, Length (Model (F, Root) (Find_Root'Result).A) + 1)
                        /= Get (Model (F, Root) (J).A, Length (Model (F, Root) (Find_Root'Result).A) + 1));

   function Find_Root (F : Forest; Root, I, J : Index_Type) return Index_Type is
      M  : constant Model_Type := Model (F, Root);
      KI : Index_Type := I;
      KJ : Index_Type := J;
   begin
      while KI /= KJ loop
         pragma Loop_Variant (Decreases => Length (M (KI).A), Decreases => Length (M (KJ).A));
         pragma Loop_Invariant (M (KI).K and then M (KI).A <= M (I).A);
         pragma Loop_Invariant (M (KJ).K and then M (KJ).A <= M (J).A);
         pragma Loop_Invariant
           (if Length (M (KI).A) > Length (M (KJ).A) then KJ = J);
         pragma Loop_Invariant
           (if Length (M (KJ).A) > Length (M (KI).A) then KI = I);
         if Length (M (KI).A) > Length (M (KJ).A) then
            KI := Parent (F, KI);
         elsif Length (M (KJ).A) > Length (M (KI).A) then
            KJ := Parent (F, KJ);
         else
            KI := Parent (F, KI);
            KJ := Parent (F, KJ);
         end if;
      end loop;
      return KI;
   end Find_Root;

   ------------------------
   -- Prove_Reverse_Peek --
   ------------------------

   procedure Prove_Reverse_Peek (F : Forest; Root, V : Index_Type; D : Direction) with
     Ghost,
     Pre => Valid_Root (F, Root) and then Model (F, Root) (V).K
     and then Peek (F, V, D) /= Empty,
     Post => Get (Model (F, Root) (Peek (F, V, D)).A, Length (Model (F, Root) (V).A) + 1) = D
   is
   begin
      null;
   end Prove_Reverse_Peek;

   --------------------------
   -- Prove_Order_No_Right --
   --------------------------

   --  The tree at Root in F has no Right children, its values are all smaller
   --  than any value V bigger than its root.

   procedure Prove_Order_No_Right (F : Forest; Root : Index_Type; Values : Value_Array; V : Natural) with
     Ghost,
     Pre  => Valid_Root (F, Root) and then Peek (F, Root, Right) = Empty and then Ordered_Leafs (F, Root, Values) and then Values (Root) < V,
     Post => All_Less_Than (F, Root, Values, V)
   is
   begin
      Prove_Model_Total (F, Root, Root, Right);
   end Prove_Order_No_Right;

   --------------------------
   -- Prove_Order_No_Left --
   --------------------------

   --  The tree at Root in F has no Left children, its values are all bigger
   --  than any value V smaller than its root.

   procedure Prove_Order_No_Left (F : Forest; Root : Index_Type; Values : Value_Array; V : Natural) with
     Ghost,
     Pre  => Valid_Root (F, Root) and then Peek (F, Root, Left) = Empty and then Ordered_Leafs (F, Root, Values) and then V < Values (Root),
     Post => All_More_Than (F, Root, Values, V)
   is
   begin
      Prove_Model_Total (F, Root, Root, Left);
   end Prove_Order_No_Left;

   -----------------------------------
   -- Prove_Correct_Place_Top_Level --
   -----------------------------------

   --  Prove that a sutree can be insert at the correct place either as the root
   --  left or right child.

   procedure Prove_Correct_Place_Top_Level (F : Forest; A : Sequence; Root, V : Index_Type; Values : Value_Array) with
     Ghost,
     Pre  => Valid_Root (F, Root) and then Valid_Root (F, V)
     and then Length (A) = 1 and then Peek (F, Root, Get (A, 1)) = Empty
     and then Ordered_Leafs (F, Root, Values)
     and then (if Get (A, 1) = Left then All_Less_Than (F, V, Values, Values (Root))
               else All_More_Than (F, V, Values, Values (Root))),
     Post => Correct_Place (F, A, Root, V, Values)
   is
   begin
      null;
   end Prove_Correct_Place_Top_Level;

   -------------------------
   -- Prove_Extract_Order --
   -------------------------

   --  State that after extraction of a subtree of F_Old rooted at V into a
   --  separate tree in F, both trees rooted at Root and V in F respect the
   --  property Ordered_Leafs, and that all values in the tree rooted at V are
   --  correctly ordered wrt all nodes on the path from Root to V in F_Old, so
   --  that they would indeed be inserted at V in a modified tree.

   procedure Prove_Extract_Order
     (F, F_Old : Forest; Root, V : Index_Type; Values : Value_Array)
   with
     Ghost,
     Global => null,
     Pre =>
       Valid_Root (F_Old, Root)
       and then Valid_Root (F, Root)
       and then Valid_Root (F, V)
       and then not Valid_Root (F_Old, V)
       and then Model (F_Old, Root) (V).K
       and then Ordered_Leafs (F_Old, Root, Values)
       and then (for all I in Index_Type =>
                  (if Model (F_Old, Root) (I).K then
                    (if Model (F_Old, Root) (V).A <= Model (F_Old, Root) (I).A
                     then Model (F, V) (I).K
                     else Model (F, Root) (I).K)))
       and then (for all I in Index_Type =>
                  (if Model (F, Root) (I).K then Model (F_Old, Root) (I).K))
       and then (for all I in Index_Type =>
                  (if V /= Empty and then Model (F, V) (I).K then Model (F_Old, Root) (I).K))
       and then (for all I in Index_Type =>
                  (if Model (F, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A))
       and then (for all I in Index_Type =>
                  (if V /= Empty and then Model (F, V) (I).K then
                     Is_Concat (Q => Model (F_Old, Root) (V).A,
                                V => Model (F, V) (I).A,
                                P => Model (F_Old, Root) (I).A))),
     Post =>
       --  The tree rooted at Root respects property Ordered_Leafs
       Ordered_Leafs (F, Root, Values)

       --  The tree rooted at V respects property Ordered_Leafs
       and then Ordered_Leafs (F, V, Values)

       --  All the nodes in the tree rooted at V are correctly ordered wrt all
       --  nodes on the path from Root to V in F_Old, so that they would indeed
       --  be inserted at V in a modified tree.
       and then Correct_Place (F, Model (F_Old, Root) (V).A, Root, V, Values)
   is
   begin
      --  First prove the last part of the postcondition

      for I in Index_Type loop
         pragma Loop_Invariant
           (for all K in 1 .. I =>
              (if Model (F, Root) (K).K
               and Model (F, Root) (K).A < Model (F_Old, Root) (V).A
               then
                 (if Get (Model (F_Old, Root) (V).A,
                  Length (Model (F, Root) (K).A) + 1) = Left
                  then All_Less_Than (F, V, Values, Values (K))
                  else All_More_Than (F, V, Values, Values (K)))));
      end loop;

      --  Then prove that the tree rooted at Root respects property
      --  Ordered_Leafs.

      for I in Index_Type loop

         --  Property Ordered_Leafs holds up to node I-1
         pragma Loop_Invariant
           (for all K in 1 .. I - 1 =>
             (for all J in Index_Type =>
               (if Model (F, Root) (K).K
                  and then Model (F, Root) (J).K
                  and then Model (F, Root) (K).A < Model (F, Root) (J).A
                then Ordered_Prefix (Model (F, Root), Values, K, J))));

         for J in Index_Type loop

            --  If I is on the path to J in the tree rooted at Root, then it
            --  was the case in F_Old, and values at I and J respect property
            --  Ordered_Leafs.
            if Model (F, Root) (I).K
              and then Model (F, Root) (J).K
              and then Model (F, Root) (I).A < Model (F, Root) (J).A
            then
               pragma Assert (Model (F_Old, Root) (I).A < Model (F_Old, Root) (J).A);
               pragma Assert (Ordered_Prefix (Model (F_Old, Root), Values, I, J));
            end if;

            --  Property Ordered_Leafs holds up to nodes I and J
            pragma Loop_Invariant
              (for all K in 1 .. J =>
                (if Model (F, Root) (I).K
                   and then Model (F, Root) (K).K
                   and then Model (F, Root) (I).A < Model (F, Root) (K).A
                 then Ordered_Prefix (Model (F, Root), Values, I, K)));
         end loop;
      end loop;

      --  Restate property Ordered_Leafs for automatic provers
      pragma Assert
        (for all K in Index_Type =>
          (for all J in Index_Type =>
            (if Model (F, Root) (K).K
               and then Model (F, Root) (J).K
               and then Model (F, Root) (K).A < Model (F, Root) (J).A
             then Ordered_Prefix (Model (F, Root), Values, K, J))));

      --  State explicitly property Ordered_Leafs for automatic provers
      pragma Assert (Ordered_Leafs (F, Root, Values));

      --  Then prove that the tree rooted at V respects property Ordered_Leafs

      for I in Index_Type loop

         --  Property Ordered_Leafs holds up to node I-1
         pragma Loop_Invariant
           (for all K in 1 .. I - 1 =>
             (for all J in Index_Type =>
               (if Model (F, V) (K).K
                  and then Model (F, V) (J).K
                  and then Model (F, V) (K).A < Model (F, V) (J).A
                then Ordered_Prefix (Model (F, V), Values, K, J))));

         for J in Index_Type loop

            --  If I is on the path to J in the tree rooted at V, then it was
            --  the case in the tree rooted at Root in F_Old, and values at I
            --  and J respect property Ordered_Leafs.
            if Model (F, V) (I).K
              and then Model (F, V) (J).K
              and then Model (F, V) (I).A < Model (F, V) (J).A
            then
               pragma Assert (Model (F_Old, Root) (I).A < Model (F_Old, Root) (J).A);
               pragma Assert (Ordered_Prefix (Model (F_Old, Root), Values, I, J));
            end if;

            --  Property Ordered_Leafs holds up to nodes I and J
            pragma Loop_Invariant
              (for all K in 1 .. J =>
                (if Model (F, V) (I).K
                   and then Model (F, V) (K).K
                   and then Model (F, V) (I).A < Model (F, V) (K).A
                 then Ordered_Prefix (Model (F, V), Values, I, K)));
         end loop;
      end loop;

      --  Restate property Ordered_Leafs for automatic provers
      pragma Assert
        (for all K in Index_Type =>
          (for all J in Index_Type =>
            (if Model (F, V) (K).K
               and then Model (F, V) (J).K
               and then Model (F, V) (K).A < Model (F, V) (J).A
             then Ordered_Prefix (Model (F, V), Values, K, J))));

      --  State explicitly property Ordered_Leafs for automatic provers
      pragma Assert (Ordered_Leafs (F, V, Values));
   end Prove_Extract_Order;

   ----------------------
   -- Prove_Plug_Order --
   ----------------------

   --  State that after plugging a tree of F_Old rooted at V into a tree rooted
   --  at Root, the combined tree rooted at Root in F respects the property
   --  Ordered_Leafs.

   procedure Prove_Plug_Order
     (F, F_Old : Forest; Root, V : Index_Type; Values : Value_Array)
   with
     Ghost,
     Global => null,
     Pre =>
       Valid_Root (F_Old, Root)
       and then Valid_Root (F, Root)
       and then Valid_Root (F_Old, V)
       and then not Valid_Root (F, V)
       and then Model (F, Root) (V).K
       and then Ordered_Leafs (F_Old, Root, Values)
       and then Ordered_Leafs (F_Old, V, Values)
       and then Correct_Place (F_Old, Model (F, Root) (V).A, Root, V, Values)
       and then (for all I in Index_Type =>
                  (if Model (F, Root) (I).K then
                    (if Model (F, Root) (V).A <= Model (F, Root) (I).A
                     then Model (F_Old, V) (I).K
                     else Model (F_Old, Root) (I).K)))
       and then (for all I in Index_Type =>
                  (if Model (F_Old, Root) (I).K then Model (F, Root) (I).K))
       and then (for all I in Index_Type =>
                  (if V /= Empty and then Model (F_Old, V) (I).K then Model (F, Root) (I).K))
       and then (for all I in Index_Type =>
                  (if Model (F_Old, Root) (I).K then Model (F_Old, Root) (I).A = Model (F, Root) (I).A))
       and then (for all I in Index_Type =>
                  (if V /= Empty and then Model (F_Old, V) (I).K then
                     Is_Concat (Q => Model (F, Root) (V).A,
                                V => Model (F_Old, V) (I).A,
                                P => Model (F, Root) (I).A))),
     Post =>
       --  The tree rooted at Root respects property Ordered_Leafs
       Ordered_Leafs (F, Root, Values)
   is
   begin
      for I in Index_Type loop

         --  Property Ordered_Leafs holds up to node I-1
         pragma Loop_Invariant
           (for all K in 1 .. I - 1 =>
             (for all J in Index_Type =>
               (if Model (F, Root) (K).K
                  and then Model (F, Root) (J).K
                  and then Model (F, Root) (K).A < Model (F, Root) (J).A
                then Ordered_Prefix (Model (F, Root), Values, K, J))));

         for J in Index_Type loop

            --  If both I and J were in the tree rooted at Root in F_Old, and
            --  I is on the path to J in the new tree, then it was the case in
            --  F_Old, and values at I and J respect property Ordered_Leafs in
            --  the new tree.
            if Model (F_Old, Root) (I).K
              and then Model (F_Old, Root) (J).K
              and then Model (F, Root) (I).A < Model (F, Root) (J).A
            then
               begin
                  pragma Assert (Model (F_Old, Root) (I).A = Model (F, Root) (I).A);
                  pragma Assert (Model (F_Old, Root) (J).A = Model (F, Root) (J).A);
                  pragma Assert (Model (F_Old, Root) (I).A < Model (F_Old, Root) (J).A);
                  pragma Assert (Ordered_Prefix (Model (F_Old, Root), Values, I, J));
                  pragma Assert_And_Cut (Ordered_Prefix (Model (F, Root), Values, I, J));
               end;
            end if;

            --  If both I and J were in the tree rooted at V in F_Old, and
            --  I is on the path to J in the new tree, then it was the case in
            --  F_Old, and values at I and J respect property Ordered_Leafs in
            --  the new tree.
            if Model (F_Old, V) (I).K
              and then Model (F_Old, V) (J).K
              and then Model (F, Root) (I).A < Model (F, Root) (J).A
            then
               begin
                  pragma Assert (Model (F_Old, V) (I).A < Model (F_Old, V) (J).A);
                  pragma Assert (Ordered_Prefix (Model (F_Old, V), Values, I, J));
                  pragma Assert_And_Cut (Ordered_Prefix (Model (F, Root), Values, I, J));
               end;
            end if;

            --  If I was in the tree rooted at Root in F_Old, and J was in the
            --  tree rooted at V in F_Old, and I is on the path to J in the
            --  new tree, then V is on this path, and values at I and J respect
            --  property Ordered_Leafs in the new tree.
            if Model (F_Old, Root) (I).K
              and then Model (F_Old, V) (J).K
              and then Model (F, Root) (I).A < Model (F, Root) (J).A
            then
               begin
                  --  Use Prove_Model_Distinct to prove that the trees rooted
                  --  at Root and V in F_Old share no nodes. As both I and V are
                  --  on the path to J, one of them comes first. If V was on the
                  --  path to I, then by a part of the precondition, I would have
                  --  to come from the tree rooted at V in F_Old, but this is
                  --  impossible as I already comes from the tree rooted at Root in
                  --  F_Old, and these trees share no nodes. Hence I is on the path
                  --  to V.

                  pragma Assert (Model (F, Root) (V).A <= Model (F, Root) (J).A);
                  begin
                     Prove_Model_Distinct (F_Old, Root, V);
                     pragma Assert_And_Cut (Model (F_Old, Root) (I).A < Model (F, Root) (V).A);
                  end;
                  pragma Assert (Get (Model (F, Root) (J).A, Length (Model (F, Root) (I).A) + 1) =
                                   Get (Model (F, Root) (V).A, Length (Model (F, Root) (I).A) + 1));

                  pragma Assert_And_Cut (Ordered_Prefix (Model (F, Root), Values, I, J));
               end;
            end if;

            --  If I was in the tree rooted at V in F_Old, and J was in the tree
            --  rooted at Root in F_Old, then I cannot be on the path to J in
            --  the new tree.
            if Model (F_Old, V) (I).K
              and then Model (F_Old, Root) (J).K
            then
               --  Use Prove_Model_Distinct to prove that the trees rooted at
               --  Root and V in F_Old share no nodes.

               Prove_Model_Distinct (F_Old, Root, V);

               --  If I was on the path to J, then by a part of the
               --  precondition, J would have to come from the tree rooted at V
               --  in F_Old, but this is impossible as J already comes from the
               --  tree rooted at Root in F_Old, and these trees share no nodes.

               pragma Assert (not (Model (F, Root) (I).A < Model (F, Root) (J).A));
            end if;

            --  Property Ordered_Leafs holds up to nodes I and J
            pragma Loop_Invariant
              (for all K in 1 .. J =>
                (if Model (F, Root) (I).K
                   and then Model (F, Root) (K).K
                   and then Model (F, Root) (I).A < Model (F, Root) (K).A
                 then (Ordered_Prefix (Model (F, Root), Values, I, K))));
         end loop;
      end loop;
   end Prove_Plug_Order;

   -----------------------------------
   -- Prove_Preserved_Correct_Place --
   -----------------------------------

   --  If the tree routed at Root in F1 and F2 is the same, and the tree rooted
   --  at V1 in F1 can be inserted at path A in it, then a tree rooted at V2 in
   --  F2 holding the same values can also be inserted at path A.
   procedure Prove_Preserve_Correct_Place
     (F1, F2 : Forest; A : Sequence; Root, V1, V2 : Index_Type; Values : Value_Array)
   with
     Ghost,
     Pre => Correct_Place (F1, A, Root, V1, Values)
     and then Valid_Root (F2, Root) and then Valid_Root (F2, V2)
     and then Model (F1, Root) = Model (F2, Root)
     and then (for all I in Index_Type =>
                 (if Model (F2, V2) (I).K then Model (F1, V1) (I).K)),
     Post => Correct_Place (F2, A, Root, V2, Values)
   is
   begin
      for I in Index_Type loop
         if Model (F2, Root) (I).K and then Model (F2, Root) (I).A < A then
            pragma Assert (Model (F1, Root) (I).K and Model (F1, Root) (I).A < A);
            if Get (A, Length (Model (F2, Root) (I).A) + 1) = Left then
               pragma Assert (Get (A, Length (Model (F1, Root) (I).A) + 1) = Left);
               pragma Assert (All_Less_Than (F1, V1, Values, Values (I)));
               pragma Assert (All_Less_Than (F2, V2, Values, Values (I)));
            else
               pragma Assert (Get (A, Length (Model (F1, Root) (I).A) + 1) = Right);
               pragma Assert (All_More_Than (F1, V1, Values, Values (I)));
               pragma Assert (All_More_Than (F2, V2, Values, Values (I)));
            end if;
         end if;
         pragma Loop_Invariant
           (for all K in 1 .. I =>
              (if Model (F2, Root) (K).K and then Model (F2, Root) (K).A < A
               then
                 (if Get (A, Length (Model (F2, Root) (K).A) + 1) = Left
                  then All_Less_Than (F2, V2, Values, Values (K))
                  else All_More_Than (F2, V2, Values, Values (K)))));
      end loop;
   end Prove_Preserve_Correct_Place;

   ---------------------------
   -- Prove_Preserved_Order --
   ---------------------------

   --  State that an unmodified tree between two forests preserved the property
   --  Ordered_Leafs.

   procedure Prove_Preserved_Order
     (F1, F2 : Forest; Root : Index_Type; Values : Value_Array)
   with
     Ghost,
     Global => null,
     Pre =>
       --  Root is the root of a tree in F1 and F2
       Valid_Root (F1, Root)
       and then Valid_Root (F2, Root)

       --  The tree rooted at Root in F2 respects the property Ordered_Leafs
       and then Ordered_Leafs (F2, Root, Values)

       --  The trees rooted at Root in F1 and F2 are the same
       and then Model (F2, Root) = Model (F1, Root),
     Post =>
       --  The tree rooted at Root in F1 respects the property Ordered_Leafs
       Ordered_Leafs (F1, Root, Values)
   is
   begin
      pragma Assert
        (for all I in Index_Type =>
          (for all J in Index_Type =>
            (if Model (F1, Root) (I).K
               and then Model (F1, Root) (J).K
               and then Model (F1, Root) (I).A < Model (F1, Root) (J).A
             then Model (F2, Root) (I).K
               and then Model (F2, Root) (J).K
               and then Model (F2, Root) (I).A < Model (F2, Root) (J).A
               and then Get (Model (F1, Root) (J).A, Length (Model (F1, Root) (I).A) + 1)
                      = Get (Model (F2, Root) (J).A, Length (Model (F2, Root) (I).A) + 1))));
      pragma Assert
        (for all I in Index_Type =>
          (for all J in Index_Type =>
            (if Model (F1, Root) (I).K
               and then Model (F1, Root) (J).K
               and then Model (F1, Root) (I).A < Model (F1, Root) (J).A
             then (if Get (Model (F1, Root) (J).A,
                           Length (Model (F1, Root) (I).A) + 1)
                      = Left
                   then Values (J) < Values (I)
                   else Values (J) > Values (I)))));
   end Prove_Preserved_Order;

   ----------------------------
   -- Prove_Preserved_Values --
   ----------------------------

   --  State that two trees with the same nodes, and same internal array of
   --  values, have the same logical set of values.

   procedure Prove_Preserved_Values (T1, T2 : Search_Tree) with
     Ghost,
     Global => null,
     Pre  =>
       T1.Root /= Empty
       and then Valid_Root (T1.Struct, T1.Root)
       and then T2.Root /= Empty
       and then Valid_Root (T2.Struct, T2.Root)
       and then Ordered_Leafs (T1.Struct, T1.Root, T1.Values)
       and then Ordered_Leafs (T2.Struct, T2.Root, T2.Values)
       and then (for all I in Index_Type =>
                  (if Model (T1.Struct, T1.Root) (I).K
                   then Model (T2.Struct, T2.Root) (I).K))
       and then (for all I in Index_Type =>
                  (if Model (T2.Struct, T2.Root) (I).K
                   then Model (T1.Struct, T1.Root) (I).K))
       and then T1.Values = T2.Values,
     Post =>
       Values (T1) = Values (T2)
   is
   begin
      null;
   end Prove_Preserved_Values;

   -----------------------
   -- Prove_Order_Total --
   -----------------------

   --  State that a value which is not found on the path to leaf L, which should
   --  have been taken to find it, is necessarily absent from the whole tree.

   procedure Prove_Order_Total (T : Search_Tree; L : Index_Type; V : Natural)
   with
     Ghost,
     Global => null,
     Pre  =>
       --  The tree is not empty
       Size (T.Struct) > 0

       --  Repeat relevant parts of the search tree invariant
       and then T.Root /= Empty
       and then Valid_Root (T.Struct, T.Root)
       and then Ordered_Leafs (T.Struct, T.Root, T.Values)

       --  V is not found at the leaf
       and then T.Values (L) /= V

       --  The leaf L is in the tree, and does not have the correct child for
       --  continuing the search for V.
       and then Model (T.Struct, T.Root) (L).K
       and then (if V < T.Values (L) then Peek (T.Struct, L, Left) = Empty
                 else Peek (T.Struct, L, Right) = Empty)

       --  V is less than all the left ancestors up to L and greater than all
       --  the right ancestors up to L.
       and then (for all I in Index_Type =>
                  (if Model (T.Struct, T.Root) (I).K then
                    (if Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (L).A
                     then (if Get (Model (T.Struct, T.Root) (L).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left
                           then V < T.Values (I)
                           else V > T.Values (I))))),
     Post =>
       (for all I in Index_Type =>
         (if Model (T.Struct, T.Root) (I).K then T.Values (I) /= V))
   is
   begin
      --  Given a node I which has L on its path, use Prove_Model_Total
      --  to prove that it is necessarily on the other side of where V would be
      --  found.

      if V < T.Values (L) then
         Prove_Model_Total (T.Struct, T.Root, L, Left);
      else
         Prove_Model_Total (T.Struct, T.Root, L, Right);
      end if;
      pragma Assert
        (for all I in Index_Type =>
           (if Model (T.Struct, T.Root) (I).K and then Find_Root (T.Struct, T.Root, I, L) = L
            then T.Values (I) /= V));
   end Prove_Order_Total;

   -----------------
   -- Left_Rotate --
   -----------------

   procedure Left_Rotate (T : in out Search_Tree; I : Index_Type) is
      X, Y    : Index_Type;
      YL      : Extended_Index_Type;
      Is_Root : constant Boolean := I = T.Root;
      J       : Index_Type := 1;
      D       : Direction := Left;

      --  Save a copy of the tree and forest on entry for use in assertions
      T_Old   : Search_Tree := T with Ghost;
      F_Old   : Forest := T.Struct with Ghost;

      --  Ghost variables to save intermediate versions of the forest, for use
      --  in assertions.
      Dummy_1, Dummy_2, Dummy_3, Dummy_4, Dummy_5 : Forest with Ghost;

      --  The proof of preservation of order and values at each step of the
      --  algorithm is isolated in local ghost lemmas Prove_XXX. None of these
      --  have a contract, so that they can be inlined during proof.

      procedure Prove_Extract_X with Ghost is
      begin
         begin
            --  Use Prove_Extract_Order to prove that the trees rooted at T.Root
            --  and X respect the property Ordered_Leafs, and that values in the
            --  tree rooted at X are as expected for reinsertion of X as left child
            --  of Y.

            if not Is_Root then
               Prove_Extract_Order (T.Struct, F_Old, T.Root, X, T.Values);
            end if;
            pragma Assert_And_Cut
              (Ordered_Leafs (T.Struct, T.Root, T.Values)
               and then Ordered_Leafs (T.Struct, X, T.Values)
               and then (for all I in Index_Type =>
                             Model (F_Old, Root (T)) (I).K =
                         (Model (T.Struct, Root (T)) (I).K or Model (T.Struct, X) (I).K)));
         end;
         Dummy_1 := T.Struct;
      end Prove_Extract_X;

      procedure Prove_Extract_Y with Ghost is
      begin
         begin
            --  Use Prove_Extract_Order to prove that the trees rooted at X and
            --  Y respect the property Ordered_Leafs.

            Prove_Extract_Order (T.Struct, Dummy_1, X, Y, T.Values);
            pragma Assert (Get (Model (Dummy_1, X) (Y).A, 1) = Right);
            pragma Assert (T.Values (X) < T.Values (Y));
            pragma Assert (All_More_Than (T.Struct, Y, T.Values, T.Values (X)));

            --  Use Prove_Preserved_Order to prove that the tree rooted at T.Root
            --  still respects the property Ordered_Leafs.

            if not Is_Root then
               Prove_Preserved_Order (T.Struct, Dummy_1, T.Root, T.Values);
            end if;

            pragma Assert_And_Cut
              (Ordered_Leafs (T.Struct, T.Root, T.Values)
               and then Ordered_Leafs (T.Struct, X, T.Values)
               and then Ordered_Leafs (T.Struct, Y, T.Values)
               and then Peek (T.Struct, X, Right) = Empty
               and then All_More_Than (T.Struct, Y, T.Values, T.Values (X))
               and then (if not Is_Root then Model (T.Struct, T.Root) = Model (Dummy_1, T.Root))
               and then (for all I in Index_Type =>
                             Model (Dummy_1, X) (I).K =
                         (Model (T.Struct, X) (I).K or Model (T.Struct, Y) (I).K)));
         end;
         Dummy_2 := T.Struct;
      end Prove_Extract_Y;

      procedure Prove_Extract_YL with Ghost is
      begin
         begin
            --  Use Prove_Extract_Order to prove that the trees rooted at Y and
            --  YL respect the property Ordered_Leafs.

            if YL /= Empty then
               Prove_Extract_Order (T.Struct, Dummy_2, Y, YL, T.Values);
               pragma Assert (Get (Model (Dummy_2, Y) (YL).A, 1) = Left);

               --  In the case where extraction did nothing, use Prove_Preserved_Order
               --  to prove that the tree rooted at Y still respects the property
               --  Ordered_Leafs.

            else
               Prove_Preserved_Order (T.Struct, Dummy_2, Y, T.Values);
            end if;

            --  Use Prove_Preserved_Order to prove that the trees rooted at T.Root
            --  and X still respect the property Ordered_Leafs.

            Prove_Preserved_Order (T.Struct, Dummy_2, X, T.Values);
            if not Is_Root then
               Prove_Preserved_Order (T.Struct, Dummy_2, T.Root, T.Values);
            end if;

            pragma Assert_And_Cut
              (Ordered_Leafs (T.Struct, T.Root, T.Values)
               and then Ordered_Leafs (T.Struct, X, T.Values)
               and then Ordered_Leafs (T.Struct, Y, T.Values)
               and then (if YL /= Empty then Ordered_Leafs (T.Struct, YL, T.Values))
               and then Peek (T.Struct, X, Right) = Empty
               and then All_More_Than (T.Struct, Y, T.Values, T.Values (X))
               and then Peek (T.Struct, Y, Left) = Empty
               and then (if YL /= Empty then All_Less_Than (T.Struct, YL, T.Values, T.Values (Y)))
               and then (if not Is_Root then Model (T.Struct, T.Root) = Model (Dummy_1, T.Root))
               and then (for all I in Index_Type =>
                             Model (Dummy_1, X) (I).K =
                         (Model (T.Struct, X) (I).K or Model (T.Struct, Y) (I).K or (YL /= Empty and then Model (T.Struct, YL) (I).K))));
         end;
         Dummy_3 := T.Struct;
      end Prove_Extract_YL;

      procedure Prove_Plug_YL with Ghost is
      begin
         begin
            --  Prove that all elements of X are smaller than Y

            Prove_Order_No_Right (Dummy_3, X, T.Values, T.Values (Y));

            if YL /= Empty then

               --  YL becomes the right child of X
               pragma Assert (Get (Model (T.Struct, X) (YL).A, 1) = Right);

               --  Use Prove_Plug_Order to prove that the combined tree respects
               --  the property Ordered_Leafs.

               Prove_Correct_Place_Top_Level (Dummy_3, Model (T.Struct, X) (YL).A, X, YL, T.Values);
               Prove_Plug_Order (T.Struct, Dummy_3, X, YL, T.Values);

            --  In the case where plugging did nothing, use Prove_Preserved_Order
            --  to prove that the tree rooted at X still respects the property
            --  Ordered_Leafs.

            else
               Prove_Preserved_Order (T.Struct, Dummy_3, X, T.Values);
            end if;

            --  Use Prove_Preserved_Order to prove that the trees rooted at T.Root
            --  and Y still respect the property Ordered_Leafs.

            Prove_Preserved_Order (T.Struct, Dummy_3, Y, T.Values);
            if not Is_Root then
               Prove_Preserved_Order (T.Struct, Dummy_3, T.Root, T.Values);
            end if;

            pragma Assert_And_Cut
              (Ordered_Leafs (T.Struct, T.Root, T.Values)
               and then Ordered_Leafs (T.Struct, X, T.Values)
               and then Ordered_Leafs (T.Struct, Y, T.Values)
               and then All_Less_Than (T.Struct, X, T.Values, T.Values (Y))
               and then Peek (T.Struct, Y, Left) = Empty
               and then (if not Is_Root then Model (T.Struct, T.Root) = Model (Dummy_1, T.Root))
               and then (for all I in Index_Type =>
                             Model (Dummy_1, X) (I).K =
                         (Model (T.Struct, X) (I).K or Model (T.Struct, Y) (I).K)));
         end;
         Dummy_4 := T.Struct;
      end Prove_Plug_YL;

      procedure Prove_Plug_X with Ghost is
      begin
         begin
            --  Use Prove_Plug_Order to prove that the combined tree respects the
            --  property Ordered_Leafs.

            Prove_Reverse_Peek (T.Struct, Y, Y, Left);

            Prove_Correct_Place_Top_Level (Dummy_4, Model (T.Struct, Y) (X).A, Y, X, T.Values);
            Prove_Plug_Order (T.Struct, Dummy_4, Y, X, T.Values);

            --  Use Prove_Preserved_Order to prove that the tree rooted at T.Root
            --  still respects the property Ordered_Leafs.

            if not Is_Root then
               Prove_Preserved_Order (T.Struct, Dummy_4, T.Root, T.Values);
            end if;

            pragma Assert_And_Cut
              ((if not Is_Root then Ordered_Leafs (T.Struct, T.Root, T.Values))
               and then Ordered_Leafs (T.Struct, Y, T.Values)
               and then (if not Is_Root then Model (T.Struct, T.Root) = Model (Dummy_1, T.Root))
               and then (for all I in Index_Type =>
                             Model (Dummy_1, X) (I).K = Model (T.Struct, Y) (I).K));
         end;
         Dummy_5 := T.Struct;
      end Prove_Plug_X;

      procedure Prove_Plug_Y with Ghost is
      begin
         begin
            --  Use Preserve_Equal to prove that the path from Root to Y is the
            --  same as the original path from Root to X.

            pragma Assert (Model (Dummy_5, T.Root) = Model (Dummy_1, T.Root));
            Preserve_Equal (S1 => Model (T.Struct, T.Root) (J).A,
                            S2 => Model (F_Old, T.Root) (J).A,
                            S3 => Model (T.Struct, T.Root) (Y).A,
                            S4 => Model (F_Old, T.Root) (X).A,
                            D  => D);

            --  Y as the same values of X, it can be inserted in its place

            Prove_Extract_Order (Dummy_1, F_Old, T.Root, X, T.Values);
            Prove_Preserve_Correct_Place
               (Dummy_1, Dummy_5, Model (F_Old, T.Root) (X).A, T.Root, X, Y, T.Values);

            --  Use Prove_Plug_Order to prove that the combined tree respects the
            --  property Ordered_Leafs.

            Prove_Plug_Order (T.Struct, Dummy_5, T.Root, Y, T.Values);
            pragma Assert_And_Cut
              (Valid_Root (T.Struct, T.Root)
               and then Ordered_Leafs (T.Struct, T.Root, T.Values)
               and then (for all I in Index_Type =>
                             Model (F_Old, T.Root) (I).K =
                           Model (T.Struct, T.Root) (I).K));
         end;
      end Prove_Plug_Y;

   begin
      --  X is the subtree located at I. Extract it as a separate tree. If X is
      --  not a root, J is its parent.

      if Is_Root then
         X := T.Root;
      else
         J := Parent (T.Struct, I);
         D := Position (T.Struct, I);
         Extract (T.Struct, T.Root, J, D, X);
      end if;
      Prove_Extract_X;

      --  Y is the right subtree of X. Extract it as a separate tree.

      Extract (T.Struct, X, X, Right, Y);
      Prove_Extract_Y;

      --  YL is the left subtree of Y. Extract it as a separate tree.

      Extract (T.Struct, Y, Y, Left, YL);
      Prove_Extract_YL;

      --  Plug YL as the right subtree of X

      Plug (T.Struct, X, X, Right, YL);
      Prove_Plug_YL;

      --  Plug X as the left subtree of Y

      Plug (T.Struct, Y, Y, Left, X);
      Prove_Plug_X;

      --  Y takes the place of X in the tree

      if Is_Root then
         T.Root := Y;
      else
         Plug (T.Struct, T.Root, J, D, Y);
         Prove_Plug_Y;
      end if;

      Prove_Preserved_Values (T_Old, T);
      pragma Assert (for all J in Index_Type =>
                       (if J not in X | Y | YL
                        then Parent (T, J) = Parent (T_Old, J)
                        and then (if Parent (T, J) /= Empty then Position (T, J) = Position (T_Old, J))));
      pragma Assert (for all I in Index_Type =>
                       (for all C in Direction =>
                          (if Size (T) /= 0 and then Model (T) (I).K
                           and then (I /= J or else D /= C)
                           and then (I /= X or else C /= Right)
                           and then (I /= Y or else C /= Left)
                        then Peek (T, I, C) = Peek (T_Old, I, C))));
   end Left_Rotate;

   ------------------
   -- Right_Rotate --
   ------------------

   procedure Right_Rotate (T : in out Search_Tree; I : Index_Type) is
      X, Y    : Index_Type;
      XR      : Extended_Index_Type;
      Is_Root : constant Boolean := I = Root (T);
      J       : Index_Type := 1;
      D       : Direction := Left;

      --  Save a copy of the tree and forest on entry for use in assertions
      T_Old   : Search_Tree := T with Ghost;
      F_Old   : Forest := T.Struct with Ghost;

      --  Ghost variables to save intermediate versions of the forest, for use
      --  in assertions.
      Dummy_1, Dummy_2, Dummy_3, Dummy_4, Dummy_5 : Forest := T.Struct with Ghost;

      --  The proof of each step of the algorithm is isolated in local ghost
      --  lemmas Prove_XXX. None of these have a contract, so that they can
      --  be inlined during proof.

      procedure Prove_Extract_Y with Ghost is
      begin
         begin
            --  Use Prove_Extract_Order to prove that the trees rooted at T.Root
            --  and Y respect the property Ordered_Leafs.

            if not Is_Root then
               Prove_Extract_Order (T.Struct, F_Old, T.Root, Y, T.Values);
            end if;
            pragma Assert_And_Cut
              (Ordered_Leafs (T.Struct, T.Root, T.Values)
               and then Ordered_Leafs (T.Struct, Y, T.Values)
               and then (for all I in Index_Type =>
                             Model (F_Old, Root (T)) (I).K =
                         (Model (T.Struct, Root (T)) (I).K or Model (T.Struct, Y) (I).K)));
         end;
         Dummy_1 := T.Struct;
      end Prove_Extract_Y;

      procedure Prove_Extract_X with Ghost is
      begin
         begin
            --  Use Prove_Extract_Order to prove that the trees rooted at X and
            --  Y respect the property Ordered_Leafs.

            Prove_Extract_Order (T.Struct, Dummy_1, Y, X, T.Values);
            pragma Assert (Get (Model (Dummy_1, Y) (X).A, 1) = Left);
            pragma Assert (T.Values (X) < T.Values (Y));
            pragma Assert (All_Less_Than (T.Struct, X, T.Values, T.Values (Y)));

            --  Use Prove_Preserved_Order to prove that the tree rooted at T.Root
            --  still respects the property Ordered_Leafs.

            if not Is_Root then
               Prove_Preserved_Order (T.Struct, Dummy_1, T.Root, T.Values);
            end if;

            pragma Assert_And_Cut
              (Ordered_Leafs (T.Struct, T.Root, T.Values)
               and then Ordered_Leafs (T.Struct, X, T.Values)
               and then Ordered_Leafs (T.Struct, Y, T.Values)
               and then Peek (T.Struct, Y, Left) = Empty
               and then All_Less_Than (T.Struct, X, T.Values, T.Values (Y))
               and then (if not Is_Root then Model (T.Struct, T.Root) = Model (Dummy_1, T.Root))
               and then (for all I in Index_Type =>
                             Model (Dummy_1, Y) (I).K =
                         (Model (T.Struct, X) (I).K or Model (T.Struct, Y) (I).K)));
         end;
         Dummy_2 := T.Struct;
      end Prove_Extract_X;

      procedure Prove_Extract_XR with Ghost is
      begin
         begin
            --  Use Prove_Extract_Order to prove that the trees rooted at X and
            --  XR respect the property Ordered_Leafs.

            if XR /= Empty then
               Prove_Extract_Order (T.Struct, Dummy_2, X, XR, T.Values);
               pragma Assert (Get (Model (Dummy_2, X) (XR).A, 1) = Right);

            --  In the case where extraction did nothing, use Prove_Preserved_Order
            --  to prove that the tree rooted at Y still respects the property
            --  Ordered_Leafs.

            else
               Prove_Preserved_Order (T.Struct, Dummy_2, X, T.Values);
            end if;

            --  Use Prove_Preserved_Order to prove that the trees rooted at T.Root
            --  and Y still respect the property Ordered_Leafs.

            Prove_Preserved_Order (T.Struct, Dummy_2, Y, T.Values);
            if not Is_Root then
               Prove_Preserved_Order (T.Struct, Dummy_2, T.Root, T.Values);
            end if;

            pragma Assert_And_Cut
              (Ordered_Leafs (T.Struct, T.Root, T.Values)
               and then Ordered_Leafs (T.Struct, X, T.Values)
               and then Ordered_Leafs (T.Struct, Y, T.Values)
               and then (if XR /= Empty then Ordered_Leafs (T.Struct, XR, T.Values))
               and then Peek (T.Struct, X, Right) = Empty
               and then All_Less_Than (T.Struct, X, T.Values, T.Values (Y))
               and then Peek (T.Struct, Y, Left) = Empty
               and then (if XR /= Empty then All_More_Than (T.Struct, XR, T.Values, T.Values (X)))
               and then (if not Is_Root then Model (T.Struct, T.Root) = Model (Dummy_1, T.Root))
               and then (for all I in Index_Type =>
                             Model (Dummy_1, Y) (I).K =
                         (Model (T.Struct, X) (I).K or Model (T.Struct, Y) (I).K or (XR /= Empty and then Model (T.Struct, XR) (I).K))));
         end;
         Dummy_3 := T.Struct;
      end Prove_Extract_XR;

      procedure Prove_Plug_XR with Ghost is
      begin
         begin
            --  Prove that all elements of Y are bigger than X

            Prove_Order_No_Left (Dummy_3, Y, T.Values, T.Values (X));

            if XR /= Empty then

               --  XR becomes the left child of Y
               pragma Assert (Get (Model (T.Struct, Y) (XR).A, 1) = Left);

               --  Use Prove_Plug_Order to prove that the combined tree respects
               --  the property Ordered_Leafs.

               Prove_Correct_Place_Top_Level (Dummy_3, Model (T.Struct, Y) (XR).A, Y, XR, T.Values);
               Prove_Plug_Order (T.Struct, Dummy_3, Y, XR, T.Values);

            --  In the case where plugging did nothing, use Prove_Preserved_Order
            --  to prove that the tree rooted at Y still respects the property
            --  Ordered_Leafs.

            else
               Prove_Preserved_Order (T.Struct, Dummy_3, Y, T.Values);
            end if;

            --  Use Prove_Preserved_Order to prove that the trees rooted at T.Root
            --  and X still respect the property Ordered_Leafs.

            Prove_Preserved_Order (T.Struct, Dummy_3, X, T.Values);
            if not Is_Root then
               Prove_Preserved_Order (T.Struct, Dummy_3, T.Root, T.Values);
            end if;

            pragma Assert_And_Cut
              (Ordered_Leafs (T.Struct, T.Root, T.Values)
               and then Ordered_Leafs (T.Struct, X, T.Values)
               and then Ordered_Leafs (T.Struct, Y, T.Values)
               and then All_More_Than (T.Struct, Y, T.Values, T.Values (X))
               and then Peek (T.Struct, X, Right) = Empty
               and then (if not Is_Root then Model (T.Struct, T.Root) = Model (Dummy_1, T.Root))
               and then (for all I in Index_Type =>
                             Model (Dummy_1, Y) (I).K =
                         (Model (T.Struct, X) (I).K or Model (T.Struct, Y) (I).K)));
         end;
         Dummy_4 := T.Struct;
      end Prove_Plug_XR;

      procedure Prove_Plug_Y with Ghost is
      begin
         begin
            --  Use Prove_Plug_Order to prove that the combined tree respects the
            --  property Ordered_Leafs.

            Prove_Reverse_Peek (T.Struct, X, X, Right);

            Prove_Correct_Place_Top_Level (Dummy_4, Model (T.Struct, X) (Y).A, X, Y, T.Values);
            Prove_Plug_Order (T.Struct, Dummy_4, X, Y, T.Values);

            --  Use Prove_Preserved_Order to prove that the tree rooted at T.Root
            --  still respects the property Ordered_Leafs.

            if not Is_Root then
               Prove_Preserved_Order (T.Struct, Dummy_4, T.Root, T.Values);
            end if;

            pragma Assert_And_Cut
              ((if not Is_Root then Ordered_Leafs (T.Struct, T.Root, T.Values))
               and then Ordered_Leafs (T.Struct, X, T.Values)
               and then (if not Is_Root then Model (T.Struct, T.Root) = Model (Dummy_1, T.Root))
               and then (for all I in Index_Type =>
                             Model (Dummy_1, Y) (I).K = Model (T.Struct, X) (I).K));
         end;
         Dummy_5 := T.Struct;
      end Prove_Plug_Y;

      procedure Prove_Plug_X with Ghost is
      begin
         begin
            --  Use Preserve_Equal to prove that the path from Root to X is the
            --  same as the original path from Root to Y.

            pragma Assert (Model (Dummy_5, T.Root) = Model (Dummy_1, T.Root));
            Preserve_Equal (S1 => Model (T.Struct, T.Root) (J).A,
                            S2 => Model (F_Old, T.Root) (J).A,
                            S3 => Model (T.Struct, T.Root) (X).A,
                            S4 => Model (F_Old, T.Root) (Y).A,
                            D  => D);

            --  X as the same values of Y, it can be inserted in its place

            Prove_Extract_Order (Dummy_1, F_Old, T.Root, Y, T.Values);
            Prove_Preserve_Correct_Place
               (Dummy_1, Dummy_5, Model (F_Old, T.Root) (Y).A, T.Root, Y, X, T.Values);

            --  Use Prove_Plug_Order to prove that the combined tree respects the
            --  property Ordered_Leafs.

            Prove_Plug_Order (T.Struct, Dummy_5, T.Root, X, T.Values);
            pragma Assert_And_Cut
              (Valid_Root (T.Struct, T.Root)
               and then Ordered_Leafs (T.Struct, T.Root, T.Values)
               and then (for all I in Index_Type =>
                             Model (F_Old, T.Root) (I).K =
                           Model (T.Struct, T.Root) (I).K));
         end;
      end Prove_Plug_X;

   begin
      --  Y is the subtree located at I. Extract it as a separate tree. If Y is
      --  not a root, J is its parent.

      if Is_Root then
         Y := T.Root;
      else
         J := Parent (T.Struct, I);
         D := Position (T.Struct, I);
         Extract (T.Struct, T.Root, J, D, Y);
      end if;
      Prove_Extract_Y;

      --  X is the left subtree of Y. Extract it as a separate tree.

      Extract (T.Struct, Y, Y, Left, X);
      Prove_Extract_X;

      --  XR is the right subtree of X. Extract it as a separate tree.

      Extract (T.Struct, X, X, Right, XR);
      Prove_Extract_XR;

      --  Plug XR as the left subtree of Y

      Plug (T.Struct, Y, Y, Left, XR);
      Prove_Plug_XR;

      --  Plug Y as the right subtree of X

      Plug (T.Struct, X, X, Right, Y);
      Prove_Plug_Y;

      --  X takes the place of Y in the tree

      if Is_Root then
         T.Root := X;
      else
         Plug (T.Struct, T.Root, J, D, X);
         Prove_Plug_X;
      end if;

      Prove_Preserved_Values (T_Old, T);
      pragma Assert (for all J in Index_Type =>
                       (if J /= X and then J /= Y and then J /= XR
                        then Parent (T, J) = Parent (T_Old, J)
                        and then (if Parent (T, J) /= Empty then Position (T, J) = Position (T_Old, J))));
      pragma Assert (for all I in Index_Type =>
                       (for all C in Direction =>
                          (if Size (T) /= 0 and then Model (T) (I).K
                           and then (I /= J or else D /= C)
                           and then (I /= X or else C /= Right)
                           and then (I /= Y or else C /= Left)
                        then Peek (T, I, C) = Peek (T_Old, I, C))));
   end Right_Rotate;

   ---------
   -- Contains --
   ---------

   function Contains (T : Search_Tree; V : Natural) return Boolean is
      Current  : Extended_Index_Type := T.Root;
      Previous : Extended_Index_Type := T.Root with Ghost;
   begin
      while Current /= Empty loop
         --  Current is in the tree
         pragma Loop_Invariant (Model (T.Struct, T.Root) (Current).K);
         pragma Loop_Variant (Increases => Length (Model (T.Struct, T.Root) (Current).A));
         --  Accumulate the knowledge that the V is less than all the left
         --  ancestors up to Current and greater than all the right ancestors
         --  up to Current.
         pragma Loop_Invariant
           (for all I in Index_Type =>
             (if Model (T.Struct, T.Root) (I).K then
               (if Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (Current).A
                then (if Get (Model (T.Struct, T.Root) (Current).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left
                      then V < T.Values (I)
                      else V > T.Values (I)))));

         Previous := Current;
         if V = T.Values (Current) then
            return True;
         elsif V < T.Values (Current) then
            Current := Peek (T.Struct, Current, Left);
         else
            Current := Peek (T.Struct, Current, Right);
         end if;
      end loop;

      --  Use Prove_Order_Total to prove that the tree cannot contain the value
      --  V.

      if Size (T.Struct) > 0 then
         Prove_Order_Total (T, Previous, V);
      end if;

      return False;
   end Contains;

   ------------
   -- Insert --
   ------------

   procedure Insert
     (T : in out Search_Tree; V : Natural; I : out Extended_Index_Type)
   is
      --  Save a copy of the tree on entry for use in assertions
      T_Old : Search_Tree := T with Ghost;

      --  The proof that the tree remains ordered is isolated in a local ghost
      --  lemma Prove_Ordered_Leafs.

      procedure Prove_Ordered_Leafs (T : Search_Tree; L : Index_Type; D : Direction) with
        Ghost,
        Global => (Input    => (T_Old, I),
                   Proof_In => V),
        Pre  =>
          --  The tree is not empty
          Size (T_Old.Struct) > 0

          --  V is not found at the leaf in T_Old
          and then T_Old.Values (L) /= V

          --  The leaf L is in the tree T_Old, and does not have the correct
          --  child for continuing the search for V.
          and then Model (T_Old.Struct, T_Old.Root) (L).K
          and then (if V < T_Old.Values (L) then D = Left else D = Right)
          and then Peek (T_Old.Struct, L, D) = Empty

          --  V is less than all the left ancestors up to L and greater than all
          --  the right ancestors up to L.
          and then (for all I in Index_Type =>
                     (if Model (T_Old.Struct, T_Old.Root) (I).K then
                       (if Model (T_Old.Struct, T_Old.Root) (I).A < Model (T_Old.Struct, T_Old.Root) (L).A
                        then (if Get (Model (T_Old.Struct, T_Old.Root) (L).A, Length (Model (T_Old.Struct, T_Old.Root) (I).A) + 1) = Left
                              then V < T_Old.Values (I)
                              else V > T_Old.Values (I)))))

          --  T is just T_Old with the additional node I as D child of L
          and then Size (T.Struct) = Size (T_Old.Struct) + 1
          and then T.Root = T_Old.Root
          and then Valid_Root (T.Struct, T.Root)
          and then I /= Empty
          and then Peek (T.Struct, L, D) = I

          --  Except for I, nodes in T and T_Old are the same
          and then (for all J in Index_Type =>
                     (if Model (T.Struct, T.Root) (J).K then
                        Model (T_Old.Struct, T.Root) (J).K or J = I))
          and then (for all J in Index_Type =>
                     (if Model (T_Old.Struct, T.Root) (J).K then Model (T.Struct, T.Root) (J).K))

          --  Except for I, nodes in T and T_Old have the same path
          and then (for all J in Index_Type =>
                     (if Model (T_Old.Struct, T.Root) (J).K
                      then Model (T.Struct, T.Root) (J).A = Model (T_Old.Struct, T.Root) (J).A))

          --  The path to I is the same as the path to L plus direction D
          and then Is_Add (Model (T.Struct, T.Root) (L).A, D, Model (T.Struct, T.Root) (I).A)

          --  Except for I, nodes in T and T_Old have the same associated values
          and then (for all J in Index_Type =>
                     (if Model (T_Old.Struct, T.Root) (J).K then T.Values (J) = T_Old.Values (J)))

          --  The value associated to node I is V
          and then T.Values (I) = V,
        Post =>
          Ordered_Leafs (T.Struct, T.Root, T.Values)
      is
      begin
         for KI in Index_Type loop

            --  Either KI is the new node I

            if KI = I then

               --  Use Prove_Model_Total to prove that any node J for which KI
               --  is on the path is necessarily on the other direction from
               --  where I has been inserted.

               Prove_Model_Total (T_Old.Struct, T.Root, L, D);

               --  Any node J for which L in on the path is necessarily on the
               --  other side of L's children wrt I.
               pragma Assert
                 (for all J in Index_Type =>
                   (if Model (T_Old.Struct, T.Root) (J).K
                      and then Model (T.Struct, T.Root) (L).A < Model (T.Struct, T.Root) (J).A
                    then Get (Model (T.Struct, T.Root) (J).A, Length (Model (T.Struct, T.Root) (L).A) + 1) /= D));

               --  The path of I is maximal wrt all other nodes in the tree
               pragma Assert
                 (for all J in Index_Type =>
                   (if Model (T.Struct, T.Root) (J).K then
                      not (Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (J).A)));

            --  Or KI was already present in the tree

            else
               --  Either J was already present in the tree, in which case we
               --  can simply restate the Ordered_Leafs property between KI and
               --  J.
               pragma Assert
                 (for all J in Index_Type =>
                   (if Model (T.Struct, T.Root) (KI).K
                      and then Model (T.Struct, T.Root) (J).K
                      and then J /= I
                      and then Model (T.Struct, T.Root) (KI).A < Model (T.Struct, T.Root) (J).A
                    then Ordered_Prefix (Model (T_Old.Struct, T_Old.Root), T_Old.Values, KI, J)));

               --  Or J is the new node I, in which case KI nodes on its path
               --  are either L or nodes on the path to L.
               pragma Assert
                 (if Model (T.Struct, T.Root) (KI).K then
                   (if Model (T.Struct, T.Root) (KI).A < Model (T.Struct, T.Root) (I).A
                    then KI = L or Model (T.Struct, T.Root) (KI).A < Model (T.Struct, T.Root) (L).A));

               --  Restate that for all nodes KI different from L, the
               --  Ordered_Leafs property holds between KI and J, which groups
               --  together the previously proved assertions. The case of KI =
               --  L was already proved when J /= I, and is immediate when J =
               --  I as then KI is the parent of J.
               pragma Assert
                 (for all J in Index_Type =>
                   (if Model (T.Struct, T.Root) (KI).K
                      and then KI /= L
                      and then Model (T.Struct, T.Root) (J).K
                      and then Model (T.Struct, T.Root) (KI).A < Model (T.Struct, T.Root) (J).A
                    then Ordered_Prefix (Model (T.Struct, T.Root), T.Values, KI, J)));
            end if;

            --  The property Ordered_Leafs is respected up to current node KI
            pragma Loop_Invariant
              (for all I in 1 .. KI =>
                (for all J in Index_Type =>
                  (if Model (T.Struct, T.Root) (I).K
                     and then Model (T.Struct, T.Root) (J).K
                     and then Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (J).A
                   then Ordered_Prefix (Model (T.Struct, T.Root), T.Values, I, J))));
         end loop;

         --  Restate property Ordered_Leafs for the last iteration of the loop
         pragma Assert
           (for all I in Index_Type =>
             (for all J in Index_Type =>
               (if Model (T.Struct, T.Root) (I).K then
                 (if Model (T.Struct, T.Root) (J).K
                     and then Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (J).A
                  then Ordered_Prefix (Model (T.Struct, T.Root), T.Values, I, J)))));
      end Prove_Ordered_Leafs;

   begin
      --  Deal with case 2: the tree is empty

      if T.Root = Empty then
         Init (T.Struct, I);
         T.Values (I) := V;
         T.Root := I;
         return;
      end if;

      --  Deal with case 1: V is already in the tree

      declare
         Current  : Extended_Index_Type := T.Root;
         Previous : Extended_Index_Type := Empty;
         D        : Direction := Left;
      begin
         while Current /= Empty loop
            --  Current is in the tree
            pragma Loop_Invariant (Model (T.Struct, T.Root) (Current).K);

            --  Accumulate the knowledge that the V is less than all the left
            --  ancestors up to Current and greater than all the right ancestors
            --  up to Current.
            pragma Loop_Invariant
              (for all I in Index_Type =>
                (if Model (T.Struct, T.Root) (I).K then
                  (if Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (Current).A
                     then (if Get (Model (T.Struct, T.Root) (Current).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left
                           then V < T.Values (I)
                           else V > T.Values (I)))));

            Previous := Current;
            if V = T.Values (Previous) then
               I := Empty;
               pragma Assert (for some I in Index_Type =>
                                Model (T) (I).K and then T.Values (I) = V);
               pragma Assert (Contains (T, V));
               return;
            elsif V < T.Values (Previous) then
               D := Left;
            else
               D := Right;
            end if;
            Current := Peek (T.Struct, Previous, D);
         end loop;

         --  Deal with case 3: the tree is not empty and V is not in it

         --  Use Prove_Order_Total to prove that the tree cannot contain the
         --  value V.

         Prove_Order_Total (T, Previous, V);

         Insert (T.Struct, T.Root, Previous, D, I);
         T.Values (I) := V;
         Prove_Ordered_Leafs (T, Previous, D);
      end;
   end Insert;

end Search_Trees;
