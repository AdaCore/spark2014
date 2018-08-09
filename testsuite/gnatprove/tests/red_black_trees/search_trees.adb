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
         pragma Loop_Invariant (Length (S) <= J);
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

   -------------------
   -- Ordered_Leafs --
   -------------------

   function Ordered_Leafs (F : Forest; Root : Index_Type; Values : Value_Array) return Boolean is
     (for all I in Index_Type =>
       (for all J in Index_Type =>
         (if Model (F, Root) (I).K
            and then Model (F, Root) (J).K
            and then Model (F, Root) (I).A < Model (F, Root) (J).A
          then (if Get (Model (F, Root) (J).A,
                        Length (Model (F, Root) (I).A) + 1)
                   = Left
                then Values (J) < Values (I)
                else Values (J) > Values (I)))));

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
         pragma Loop_Invariant (M (KJ).A <= M (J).A);
         pragma Loop_Invariant (M (KJ).K);
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
       and then (for all I in Index_Type =>
                  (if Model (F, Root) (I).K
                     and Model (F, Root) (I).A < Model (F_Old, Root) (V).A
                   then
                     (if Get (Model (F_Old, Root) (V).A,
                              Length (Model (F, Root) (I).A) + 1) = Left
                      then
                        (for all J in Index_Type =>
                          (if Model (F, V) (J).K
                           then Values (J) < Values (I)))
                      else
                        (for all J in Index_Type =>
                          (if Model (F, V) (J).K
                           then Values (J) > Values (I))))))
   is
   begin
      --  First prove that the tree rooted at Root respects property
      --  Ordered_Leafs.

      for I in Index_Type loop

         --  Property Ordered_Leafs holds up to node I-1
         pragma Loop_Invariant
           (for all K in 1 .. I - 1 =>
             (for all J in Index_Type =>
               (if Model (F, Root) (K).K
                  and then Model (F, Root) (J).K
                  and then Model (F, Root) (K).A < Model (F, Root) (J).A
                then (if Get (Model (F, Root) (J).A,
                              Length (Model (F, Root) (K).A) + 1)
                         = Left
                      then Values (J) < Values (K)
                      else Values (J) > Values (K)))));

         for J in Index_Type loop

            --  If I is on the path to J in the tree rooted at Root, then it
            --  was the case in F_Old, and values at I and J respect property
            --  Ordered_Leafs.
            if Model (F, Root) (I).K
              and then Model (F, Root) (J).K
              and then Model (F, Root) (I).A < Model (F, Root) (J).A
            then
               pragma Assert (Model (F_Old, Root) (I).A < Model (F_Old, Root) (J).A);
               pragma Assert
                 (if Get (Model (F, Root) (J).A,
                          Length (Model (F, Root) (I).A) + 1)
                     = Left
                  then Values (J) < Values (I)
                  else Values (J) > Values (I));
            end if;

            --  Property Ordered_Leafs holds up to nodes I and J
            pragma Loop_Invariant
              (for all K in 1 .. J =>
                (if Model (F, Root) (I).K
                   and then Model (F, Root) (K).K
                   and then Model (F, Root) (I).A < Model (F, Root) (K).A
                 then (if Get (Model (F, Root) (K).A,
                               Length (Model (F, Root) (I).A) + 1)
                          = Left
                       then Values (K) < Values (I)
                       else Values (K) > Values (I))));
         end loop;
      end loop;

      --  Restate property Ordered_Leafs for automatic provers
      pragma Assert
        (for all K in Index_Type =>
          (for all J in Index_Type =>
            (if Model (F, Root) (K).K
               and then Model (F, Root) (J).K
               and then Model (F, Root) (K).A < Model (F, Root) (J).A
             then (if Get (Model (F, Root) (J).A,
                           Length (Model (F, Root) (K).A) + 1)
                       = Left
                   then Values (J) < Values (K)
                   else Values (J) > Values (K)))));

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
                then (if Get (Model (F, V) (J).A,
                              Length (Model (F, V) (K).A) + 1)
                         = Left
                      then Values (J) < Values (K)
                      else Values (J) > Values (K)))));

         for J in Index_Type loop

            --  If I is on the path to J in the tree rooted at V, then it was
            --  the case in the tree rooted at Root in F_Old, and values at I
            --  and J respect property Ordered_Leafs.
            if Model (F, V) (I).K
              and then Model (F, V) (J).K
              and then Model (F, V) (I).A < Model (F, V) (J).A
            then
               pragma Assert (Model (F_Old, Root) (I).A < Model (F_Old, Root) (J).A);
               pragma Assert
                 (if Get (Model (F, V) (J).A,
                          Length (Model (F, V) (I).A) + 1)
                     = Left
                  then Values (J) < Values (I)
                  else Values (J) > Values (I));
            end if;

            --  Property Ordered_Leafs holds up to nodes I and J
            pragma Loop_Invariant
              (for all K in 1 .. J =>
                (if Model (F, V) (I).K
                   and then Model (F, V) (K).K
                   and then Model (F, V) (I).A < Model (F, V) (K).A
                 then (if Get (Model (F, V) (K).A,
                               Length (Model (F, V) (I).A) + 1)
                          = Left
                       then Values (K) < Values (I)
                       else Values (K) > Values (I))));
         end loop;
      end loop;

      --  Restate property Ordered_Leafs for automatic provers
      pragma Assert
        (for all K in Index_Type =>
          (for all J in Index_Type =>
            (if Model (F, V) (K).K
               and then Model (F, V) (J).K
               and then Model (F, V) (K).A < Model (F, V) (J).A
             then (if Get (Model (F, V) (J).A,
                           Length (Model (F, V) (K).A) + 1)
                      = Left
                   then Values (J) < Values (K)
                   else Values (J) > Values (K)))));

      --  State explicitly property Ordered_Leafs for automatic provers
      pragma Assert (Ordered_Leafs (F, V, Values));

      --  The last part of the postcondition gets proved automatically, as a
      --  consequence of the fact that property Ordered_Leafs holds for F_Old.
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
       and then (for all I in Index_Type =>
                  (if Model (F_Old, Root) (I).K
                     and Model (F_Old, Root) (I).A < Model (F, Root) (V).A
                   then (if Get (Model (F, Root) (V).A,
                                 Length (Model (F_Old, Root) (I).A) + 1) = Left
                         then
                           (for all J in Index_Type =>
                             (if Model (F_Old, V) (J).K
                              then Values (J) < Values (I)))
                         else
                           (for all J in Index_Type =>
                             (if Model (F_Old, V) (J).K
                              then Values (J) > Values (I))))))
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
                then (if Get (Model (F, Root) (J).A,
                              Length (Model (F, Root) (K).A) + 1)
                         = Left
                      then Values (J) < Values (K)
                      else Values (J) > Values (K)))));

         for J in Index_Type loop

            --  If both I and J were in the tree rooted at Root in F_Old, and
            --  I is on the path to J in the new tree, then it was the case in
            --  F_Old, and values at I and J respect property Ordered_Leafs in
            --  the new tree.
            if Model (F_Old, Root) (I).K
              and then Model (F_Old, Root) (J).K
              and then Model (F, Root) (I).A < Model (F, Root) (J).A
            then
               pragma Assert (Model (F_Old, Root) (I).A < Model (F_Old, Root) (J).A);
               pragma Assert
                 (if Get (Model (F, Root) (J).A,
                          Length (Model (F, Root) (I).A) + 1)
                     = Left
                  then Values (J) < Values (I)
                  else Values (J) > Values (I));
            end if;

            --  If both I and J were in the tree rooted at V in F_Old, and
            --  I is on the path to J in the new tree, then it was the case in
            --  F_Old, and values at I and J respect property Ordered_Leafs in
            --  the new tree.
            if Model (F_Old, V) (I).K
              and then Model (F_Old, V) (J).K
              and then Model (F, Root) (I).A < Model (F, Root) (J).A
            then
               pragma Assert (Model (F_Old, V) (I).A < Model (F_Old, V) (J).A);
               pragma Assert (Get (Model (F, Root) (J).A,
                                   Length (Model (F, Root) (I).A) + 1)
                            = Get (Model (F_Old, V) (J).A,
                                   Length (Model (F_Old, V) (I).A) + 1));
               pragma Assert
                 (if Get (Model (F, Root) (J).A,
                          Length (Model (F, Root) (I).A) + 1)
                     = Left
                  then Values (J) < Values (I)
                  else Values (J) > Values (I));
            end if;

            --  If I was in the tree rooted at Root in F_Old, and J was in the
            --  tree rooted at V in F_Old, and I is on the path to J in the
            --  new tree, then V is on this path, and values at I and J respect
            --  property Ordered_Leafs in the new tree.
            if Model (F_Old, Root) (I).K
              and then Model (F_Old, V) (J).K
              and then Model (F, Root) (I).A < Model (F, Root) (J).A
            then
               --  Use Prove_Model_Distinct to prove that the trees rooted
               --  at Root and V in F_Old share no nodes. As both I and V are
               --  on the path to J, one of them comes first. If V was on the
               --  path to I, then by a part of the precondition, I would have
               --  to come from the tree rooted at V in F_Old, but this is
               --  impossible as I already comes from the tree rooted at Root in
               --  F_Old, and these trees share no nodes. Hence I is on the path
               --  to V.

               pragma Assert (Model (F, Root) (V).A <= Model (F, Root) (J).A);
               Prove_Model_Distinct (F_Old, Root, V);
               pragma Assert (Model (F_Old, Root) (I).A < Model (F, Root) (V).A);

               --  Intermediate assertion trivially true (a tautology) which
               --  provides a useful term to instantiate the part of the
               --  precondition proving that the values at I and J respect
               --  property Ordered_Leafs.
               pragma Assert
                 (Get (Model (F, Root) (V).A, Length (Model (F, Root) (I).A) + 1)
                = Get (Model (F, Root) (V).A, Length (Model (F, Root) (I).A) + 1));
               pragma Assert
                 (if Get (Model (F, Root) (J).A,
                          Length (Model (F, Root) (I).A) + 1)
                     = Left
                  then Values (J) < Values (I)
                  else Values (J) > Values (I));
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
                 then (if Get (Model (F, Root) (K).A,
                               Length (Model (F, Root) (I).A) + 1)
                          = Left
                       then Values (K) < Values (I)
                       else Values (K) > Values (I))));
         end loop;
      end loop;

      --  Restate property Ordered_Leafs for automatic provers
      pragma Assert
        (for all I in Index_Type =>
          (for all J in Index_Type =>
            (if Model (F, Root) (I).K
               and then Model (F, Root) (J).K
               and then Model (F, Root) (I).A < Model (F, Root) (J).A
             then (if Get (Model (F, Root) (J).A,
                           Length (Model (F, Root) (I).A) + 1)
                      = Left
                   then Values (J) < Values (I)
                   else Values (J) > Values (I)))));
   end Prove_Plug_Order;

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
      --  Case 1: given a node I which does not have L on its path, consider
      --  the common ancestor of L and I returned by Find_Root. Instantiating
      --  Ordered_Leafs once with this common ancestor and L, and another time
      --  with this common ancestor and I, allows to prove that V cannot be the
      --  same as the value at I.
      pragma Assert
        (for all I in Index_Type =>
          (if Model (T.Struct, T.Root) (I).K
           then Model (T.Struct, T.Root) (Find_Root (T.Struct, T.Root, I, L)).K));

      --  Case 2: given a node I which has L on its path, use Prove_Model_Total
      --  to prove that it is necessarily on the other side of where V would be
      --  found.

      if V < T.Values (L) then
         Prove_Model_Total (T.Struct, T.Root, L, Left);
      else
         Prove_Model_Total (T.Struct, T.Root, L, Right);
      end if;
      pragma Assert
        (for all I in Index_Type =>
           (if Model (T.Struct, T.Root) (I).K
            and then Find_Root (T.Struct, T.Root, I, L) = L
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
      F_1, F_2, F_3, F_4, F_5 : Forest := T.Struct with Ghost;

      --  The proof of each step of the algorithm is isolated in local ghost
      --  lemmas Prove_XXX. None of these have a contract, so that they can
      --  be inlined during proof.

      procedure Prove_Extract_X with Ghost is
      begin
         --  Use Prove_Extract_Order to prove that the trees rooted at T.Root
         --  and X respect the property Ordered_Leafs, and that values in the
         --  tree rooted at X are as expected for reinsertion of X as left child
         --  of Y.

         if not Is_Root then
            Prove_Extract_Order (T.Struct, F_Old, T.Root, X, T.Values);
         end if;
         F_1 := T.Struct;
      end Prove_Extract_X;

      procedure Prove_Extract_Y with Ghost is
      begin
         --  Use Prove_Extract_Order to prove that the trees rooted at X and
         --  Y respect the property Ordered_Leafs, and that values in the tree
         --  rooted at Y are as expected for reinsertion of Y in the place of X.

         Prove_Extract_Order (T.Struct, F_1, X, Y, T.Values);
         pragma Assert (Get (Model (F_1, X) (Y).A, 1) = Right);
         pragma Assert (T.Values (X) < T.Values (Y));

         --  Use Prove_Preserved_Order to prove that the tree rooted at T.Root
         --  still respects the property Ordered_Leafs.

         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_1, T.Root, T.Values);
         end if;
         F_2 := T.Struct;
      end Prove_Extract_Y;

      procedure Prove_Extract_YL with Ghost is
      begin
         --  Use Prove_Extract_Order to prove that the trees rooted at Y and
         --  YL respect the property Ordered_Leafs, and that values in the tree
         --  rooted at YL are as expected for reinsertion of YL as the right
         --  child of X.

         if YL /= Empty then
            Prove_Extract_Order (T.Struct, F_2, Y, YL, T.Values);
            pragma Assert (Get (Model (F_2, Y) (YL).A, 1) = Left);

         --  In the case where extraction did nothing, use Prove_Preserved_Order
         --  to prove that the tree rooted at Y still respects the property
         --  Ordered_Leafs.

         else
            Prove_Preserved_Order (T.Struct, F_2, Y, T.Values);
         end if;

         --  Use Prove_Preserved_Order to prove that the trees rooted at T.Root
         --  and X still respect the property Ordered_Leafs.

         Prove_Preserved_Order (T.Struct, F_2, X, T.Values);
         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_2, T.Root, T.Values);
         end if;
         F_3 := T.Struct;
      end Prove_Extract_YL;

      procedure Prove_Plug_YL with Ghost is
      begin
         if YL /= Empty then

            --  YL becomes the right child of X
            pragma Assert (Get (Model (T.Struct, X) (YL).A, 1) = Right);

            --  Trees previously rooted at X and YL respect the property
            --  Ordered_Leafs, and all the values in the tree rooted at YL
            --  are greater than the value at X.
            pragma Assert
              (for all J in Index_Type =>
                (if Model (F_3, Y) (J).K
                 then T.Values (J) > T.Values (X)));
            pragma Assert (Ordered_Leafs (F_3, X, T.Values));
            pragma Assert (Ordered_Leafs (F_3, YL, T.Values));

            --  Use Prove_Plug_Order to prove that the combined tree respects
            --  the property Ordered_Leafs.

            Prove_Plug_Order (T.Struct, F_3, X, YL, T.Values);

         --  In the case where plugging did nothing, use Prove_Preserved_Order
         --  to prove that the tree rooted at X still respects the property
         --  Ordered_Leafs.

         else
            Prove_Preserved_Order (T.Struct, F_3, X, T.Values);
         end if;

         --  Use Prove_Preserved_Order to prove that the trees rooted at T.Root
         --  and Y still respect the property Ordered_Leafs.

         Prove_Preserved_Order (T.Struct, F_3, Y, T.Values);
         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_3, T.Root, T.Values);
         end if;
         F_4 := T.Struct;
      end Prove_Plug_YL;

      procedure Prove_Plug_X with Ghost is
      begin
         --  Use Prove_Model_Total to prove that any node J for which X is on
         --  the path in F_2 is necessarily on the other direction from where
         --  Y was extracted.

         pragma Assert (Get (Model (T.Struct, Y) (X).A, 1) = Left);
         Prove_Model_Total (F_2, X, X, Right);
         pragma Assert
           (for all J in Index_Type =>
              (if Model (F_3, X) (J).K
               then T.Values (J) <= T.Values (X)));
         pragma Assert
           (for all J in Index_Type =>
              (if Model (F_4, X) (J).K
               then T.Values (J) < T.Values (Y)));
         pragma Assert (Ordered_Leafs (F_4, X, T.Values));
         pragma Assert (Ordered_Leafs (F_4, Y, T.Values));

         --  Use Prove_Plug_Order to prove that the combined tree respects the
         --  property Ordered_Leafs.

         Prove_Plug_Order (T.Struct, F_4, Y, X, T.Values);

         --  Use Prove_Preserved_Order to prove that the tree rooted at T.Root
         --  still respects the property Ordered_Leafs.

         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_4, T.Root, T.Values);
         end if;
         F_5 := T.Struct;
      end Prove_Plug_X;

      procedure Prove_Plug_Y is
      begin
         --  Use Preserve_Equal to prove that the path from Root to Y is the
         --  same as the original path from Root to X.

         pragma Assert (Model (F_5, T.Root) = Model (F_1, T.Root));
         Preserve_Equal (S1 => Model (T.Struct, T.Root) (J).A,
                         S2 => Model (F_Old, T.Root) (J).A,
                         S3 => Model (T.Struct, T.Root) (Y).A,
                         S4 => Model (F_Old, T.Root) (X).A,
                         D  => D);
         pragma Assert
           (for all I in Index_Type =>
             (if Model (F_5, Y) (I).K then Model (F_1, X) (I).K));
         pragma Assert
           (for all I in Index_Type =>
             (if Model (F_5, T.Root) (I).K
                and Model (F_5, T.Root) (I).A < Model (T.Struct, T.Root) (Y).A
              then
                 Model (F_1, T.Root) (I).K
                 and Model (F_1, T.Root) (I).A < Model (F_Old, T.Root) (X).A));
         pragma Assert
           (for all I in Index_Type =>
             (if Model (F_5, T.Root) (I).K
                and Model (F_5, T.Root) (I).A < Model (T.Struct, T.Root) (Y).A
              then
                Get (Model (F_Old, T.Root) (X).A,
                     Length (Model (F_1, T.Root) (I).A) + 1)
              = Get (Model (T.Struct, T.Root) (Y).A,
                Length (Model (F_5, T.Root) (I).A) + 1)));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, T.Root) (I).K
               and Model (F_5, T.Root) (I).A < Model (T.Struct, T.Root) (Y).A
               then (if Get (Model (T.Struct, T.Root) (Y).A,
                 Length (Model (F_5, T.Root) (I).A) + 1) = Left
                 then
                   (for all J in Index_Type =>
                      (if Model (F_5, Y) (J).K
                       then T.Values (J) < T.Values (I)))
                 else
                   (for all J in Index_Type =>
                      (if Model (F_5, Y) (J).K
                       then T.Values (J) > T.Values (I))))));

         --  Use Prove_Plug_Order to prove that the combined tree respects the
         --  property Ordered_Leafs.

         Prove_Plug_Order (T.Struct, F_5, T.Root, Y, T.Values);
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
      F_1, F_2, F_3, F_4, F_5 : Forest := T.Struct with Ghost;

      --  The proof of each step of the algorithm is isolated in local ghost
      --  lemmas Prove_XXX. None of these have a contract, so that they can
      --  be inlined during proof.

      procedure Prove_Extract_Y with Ghost is
      begin
         --  Use Prove_Extract_Order to prove that the trees rooted at T.Root
         --  and Y respect the property Ordered_Leafs, and that values in the
         --  tree rooted at Y are as expected for reinsertion of Y as right
         --  child of X.

         if not Is_Root then
            Prove_Extract_Order (T.Struct, F_Old, T.Root, Y, T.Values);
         end if;
         F_1 := T.Struct;
      end Prove_Extract_Y;

      procedure Prove_Extract_X with Ghost is
      begin
         --  Use Prove_Extract_Order to prove that the trees rooted at Y and
         --  X respect the property Ordered_Leafs, and that values in the tree
         --  rooted at X are as expected for reinsertion of X in the place of Y.

         Prove_Extract_Order (T.Struct, F_1, Y, X, T.Values);
         pragma Assert (Get (Model (F_1, Y) (X).A, 1) = Left);
         pragma Assert (T.Values (X) < T.Values (Y));

         --  Use Prove_Preserved_Order to prove that the tree rooted at T.Root
         --  still respects the property Ordered_Leafs.

         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_1, T.Root, T.Values);
         end if;
         F_2 := T.Struct;
      end Prove_Extract_X;

      procedure Prove_Extract_XR with Ghost is
      begin
         --  Use Prove_Extract_Order to prove that the trees rooted at X and
         --  XR respect the property Ordered_Leafs, and that values in the tree
         --  rooted at XR are as expected for reinsertion of XR as the left
         --  child of Y.

         if XR /= Empty then
            Prove_Extract_Order (T.Struct, F_2, X, XR, T.Values);
            pragma Assert (Get (Model (F_2, X) (XR).A, 1) = Right);

         --  In the case where extraction did nothing, use Prove_Preserved_Order
         --  to prove that the tree rooted at X still respects the property
         --  Ordered_Leafs.

         else
            Prove_Preserved_Order (T.Struct, F_2, X, T.Values);
         end if;

         --  Use Prove_Preserved_Order to prove that the trees rooted at T.Root
         --  and Y still respect the property Ordered_Leafs.

         Prove_Preserved_Order (T.Struct, F_2, Y, T.Values);
         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_2, T.Root, T.Values);
         end if;
         F_3 := T.Struct;
      end Prove_Extract_XR;

      procedure Prove_Plug_XR with Ghost is
      begin
         if XR /= Empty then

            --  XR becomes the left child of Y
            pragma Assert (Get (Model (T.Struct, Y) (XR).A, 1) = Left);

            --  Trees previously rooted at Y and XR respect the property
            --  Ordered_Leafs, and all the values in the tree rooted at XR
            --  are greater than the value at Y.
            pragma Assert
              (for all J in Index_Type =>
                 (if Model (F_3, X) (J).K
                  then T.Values (J) < T.Values (Y)));
            pragma Assert (Ordered_Leafs (F_3, Y, T.Values));

            --  Use Prove_Plug_Order to prove that the combined tree respects
            --  the property Ordered_Leafs.

            Prove_Plug_Order (T.Struct, F_3, Y, XR, T.Values);

         --  In the case where plugging did nothing, use Prove_Preserved_Order
         --  to prove that the tree rooted at Y still respects the property
         --  Ordered_Leafs.

         else
            Prove_Preserved_Order (T.Struct, F_3, Y, T.Values);
         end if;

         --  Use Prove_Preserved_Order to prove that the trees rooted at T.Root
         --  and X still respect the property Ordered_Leafs.

         Prove_Preserved_Order (T.Struct, F_3, X, T.Values);
         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_3, T.Root, T.Values);
         end if;
         F_4 := T.Struct;
      end Prove_Plug_XR;

      procedure Prove_Plug_Y with Ghost is
      begin
         --  Use Prove_Model_Total to prove that any node J for which Y is on
         --  the path in F_2 is necessarily on the other direction from where
         --  X was extracted.

         pragma Assert (Get (Model (T.Struct, X) (Y).A, 1) = Right);
         Prove_Model_Total (F_2, Y, Y, Left);
         pragma Assert
           (for all J in Index_Type =>
              (if XR /= Empty and then Model (F_3, XR) (J).K
               then T.Values (J) > T.Values (X)));
         pragma Assert
           (for all J in Index_Type =>
              (if Model (F_3, Y) (J).K
               then T.Values (J) >= T.Values (Y)));
         pragma Assert
           (for all J in Index_Type =>
              (if Model (F_4, Y) (J).K
               then T.Values (J) > T.Values (X)));
         pragma Assert (Ordered_Leafs (F_4, X, T.Values));
         pragma Assert (Ordered_Leafs (F_4, Y, T.Values));

         --  Use Prove_Plug_Order to prove that the combined tree respects the
         --  property Ordered_Leafs.

         Prove_Plug_Order (T.Struct, F_4, X, Y, T.Values);

         --  Use Prove_Preserved_Order to prove that the tree rooted at T.Root
         --  still respects the property Ordered_Leafs.

         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_4, T.Root, T.Values);
         end if;
         F_5 := T.Struct;
      end Prove_Plug_Y;

      procedure Prove_Plug_X is
      begin
         --  Use Preserve_Equal to prove that the path from Root to X is the
         --  same as the original path from Root to Y.

         pragma Assert (Model (F_5, T.Root) = Model (F_1, T.Root));
         Preserve_Equal (Model (T.Struct, T.Root) (J).A, Model (F_Old, T.Root) (J).A,
                         Model (T.Struct, T.Root) (X).A, Model (F_Old, T.Root) (Y).A, D);
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, X) (I).K then Model (F_1, Y) (I).K));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, T.Root) (I).K
               and Model (F_5, T.Root) (I).A < Model (T.Struct, T.Root) (X).A then
                    Model (F_1, T.Root) (I).K
               and Model (F_1, T.Root) (I).A < Model (F_Old, T.Root) (Y).A));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, T.Root) (I).K
               and Model (F_5, T.Root) (I).A < Model (T.Struct, T.Root) (X).A then
               Length (Model (F_1, T.Root) (I).A) = Length (Model (F_5, T.Root) (I).A)));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, T.Root) (I).K
               and Model (F_5, T.Root) (I).A < Model (T.Struct, T.Root) (X).A then
               Get (Model (F_Old, T.Root) (Y).A,
                 Length (Model (F_5, T.Root) (I).A) + 1)
               = Get (Model (T.Struct, T.Root) (X).A,
                 Length (Model (F_5, T.Root) (I).A) + 1)));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, T.Root) (I).K
               and Model (F_5, T.Root) (I).A < Model (T.Struct, T.Root) (X).A then
               Get (Model (F_Old, T.Root) (Y).A,
                 Length (Model (F_1, T.Root) (I).A) + 1)
               = Get (Model (T.Struct, T.Root) (X).A,
                 Length (Model (F_5, T.Root) (I).A) + 1)));
         pragma Assert (Ordered_Leafs (F_5, T.Root, T.Values));
         pragma Assert (Ordered_Leafs (F_4, X, T.Values));

         --  Use Prove_Plug_Order to prove that the combined tree respects the
         --  property Ordered_Leafs.

         Prove_Plug_Order (T.Struct, F_5, T.Root, X, T.Values);
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

      pragma Assert
        (for all J in Index_Type =>
          (if Model (T_Old) (J).K then Model (T) (J).K));
      Prove_Preserved_Values (T_Old, T);
   end Right_Rotate;

   ---------
   -- Contains --
   ---------

   function Contains (T : Search_Tree; V : Natural) return Boolean is
      Current  : Extended_Index_Type := T.Root;
      Previous : Extended_Index_Type := T.Root with Ghost;
      D        : Direction := Left with Ghost;
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
            D := Left;
            Current := Peek (T.Struct, Current, Left);
         else
            D := Right;
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
                    then (if Get (Model (T.Struct, T.Root) (J).A, Length (Model (T.Struct, T.Root) (KI).A) + 1) = Left
                          then T.Values (J) < T.Values (KI)
                          else T.Values (J) > T.Values (KI))));

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
                    then (if Get (Model (T.Struct, T.Root) (J).A, Length (Model (T.Struct, T.Root) (KI).A) + 1) = Left
                          then T.Values (J) < T.Values (KI)
                          else T.Values (J) > T.Values (KI))));
            end if;

            --  The property Ordered_Leafs is respected up to current node KI
            pragma Loop_Invariant
              (for all I in 1 .. KI =>
                (for all J in Index_Type =>
                  (if Model (T.Struct, T.Root) (I).K
                     and then Model (T.Struct, T.Root) (J).K
                     and then Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (J).A
                   then (if Get (Model (T.Struct, T.Root) (J).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left
                         then T.Values (J) < T.Values (I)
                         else T.Values (J) > T.Values (I)))));
         end loop;

         --  Restate property Ordered_Leafs for the last iteration of the loop
         pragma Assert
           (for all I in Index_Type =>
             (for all J in Index_Type =>
               (if Model (T.Struct, T.Root) (I).K then
                 (if Model (T.Struct, T.Root) (J).K
                     and then Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (J).A
                  then (if Get (Model (T.Struct, T.Root) (J).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left
                        then T.Values (J) < T.Values (I)
                        else T.Values (J) > T.Values (I))))));
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
