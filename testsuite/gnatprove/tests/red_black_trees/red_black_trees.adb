package body Red_Black_Trees with SPARK_Mode is

   type Black_Count is record
      Status : Boolean;
      Depth  : Extended_Index_Type;
      Count  : Extended_Index_Type;
   end record;
   --  Structure storing information about branches leaving a node.
   --  Count stores the number of black nodes in the left-most branch leaving
   --  the node.
   --  Depth stores the maximum size of branches leaving the node. It is used
   --  to perform induction on branches starting from the leafs.
   --  Status is True if and only if the node's left and right children have the
   --  same value for Count.

   function Eq (X, Y : Black_Count) return Boolean is
     (X.Status = Y.Status and X.Count = Y.Count)
   with Post => Eq'Result in Boolean;
   --  Equivalence between Black_Counts. The Depth field is ignored here.

   type Count_Array is array (Extended_Index_Type) of Black_Count;

   function Nb_Blacks (T : Rbt) return Count_Array with
     --  Function that computes a Black_Count for each node reachable in a tree

     Ghost,
     Pre  => Size (T.Struct) /= 0,
     Post =>

       --  Empty has Depth and Count 0
       Nb_Blacks'Result (Empty) = (True, 0, 0)

       --  For reachable nodes in T, Status is True if and only if the node's
       --  left and right children have the same value for Count.
       and (for all I in Index_Type =>
               (if Model (T.Struct) (I).K then
                     Nb_Blacks'Result (I).Status =
                 (Nb_Blacks'Result (Peek (T.Struct, I, Left)).Count
                   = Nb_Blacks'Result (Peek (T.Struct, I, Right)).Count)

                 --  Depth is one more than the maximal Depth of the node children
                 and Nb_Blacks'Result (I).Depth = 1 + Extended_Index_Type'Max
                 (Nb_Blacks'Result (Peek (T.Struct, I, Left)).Depth,
                   Nb_Blacks'Result (Peek (T.Struct, I, Right)).Depth)

                 --  Count is the Count of its left child if node is red and
                 --  one more than this Count if node is black.
                 and Nb_Blacks'Result (I).Count =
                 (if T.Color (I) = Black then 1 else 0)
                 + Nb_Blacks'Result (Peek (T.Struct, I, Left)).Count))
   is
      Res : Count_Array :=
        (Empty => (True, 0, 0), others => (False, Max, Max));
      --  The result of the call. Except for Empty, the Depth of each node is
      --  initialized to Max so that we can tell the difference between
      --  computed values and default ones.

      M   : constant Model_Type := Model (T.Struct);

   begin
      --  Loop Max times over M to compute values for Res. At each iteration,
      --  compute Black_Count for nodes that have a Depth of N + 1.

      for N in Extended_Index range 0 .. Max - 1 loop

         --  The Black_Count of Empty is not modified in the loop
         pragma Loop_Invariant (Res (Empty) = (True, 0, 0));

         --  For each node, the value of Count is smaller than the value of Depth
         pragma Loop_Invariant
           (for all I in Index_Type => Res (I).Count <= Res (I).Depth);

         --  For already handled nodes, the value of Depth is smaller than N
         pragma Loop_Invariant
           (for all I in Index_Type =>
              Res (I).Depth = Max or Res (I).Depth <= N);

         --  Nodes that are not handled yet must have a path smaller than
         --  Max - N. The computed Black_Count of other nodes have the
         --  expected property.
         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if M (I).K and Res (I).Depth > N then
                    Last (M (I).A) < Max - N
               elsif M (I).K then
                    Res (I).Depth <= N
               and Res (I).Status =
                   (Res (Peek (T.Struct, I, Left)).Count
                  = Res (Peek (T.Struct, I, Right)).Count)
               and Res (I).Depth = 1 + Extended_Index_Type'Max
                   (Res (Peek (T.Struct, I, Left)).Depth,
                    Res (Peek (T.Struct, I, Right)).Depth)
               and Res (I).Count =
                   (if T.Color (I) = Black then 1 else 0)
                      + Res (Peek (T.Struct, I, Left)).Count));

         --  We have already handled all reachable nodes that have children of
         --  Depth strictly smaller than N.
         pragma Loop_Invariant
           (for all J in Index_Type =>
              (if M (J).K
               and then Res (Peek (T.Struct, J, Left)).Depth < N
               and then Res (Peek (T.Struct, J, Right)).Depth < N then
                  Res (J).Depth <= N));

         for I in Index_Type loop

            --  The value of Empty is not modified in the loop
            pragma Loop_Invariant (Res (Empty) = (True, 0, 0));

            --  For each node, the value of Count is smaller than the value of Depth
            pragma Loop_Invariant
              (for all I in Index_Type => Res (I).Count <= Res (I).Depth);

            --  For already handled nodes, the value of Depth is smaller than
            --  N + 1 if they are located before I and smaller than N otherwise.
            pragma Loop_Invariant
              (for all J in 1 .. I - 1 =>
                 Res (J).Depth = Max or Res (J).Depth <= N + 1);
            pragma Loop_Invariant
              (for all J in I .. Max =>
                 Res (J).Depth = Max or Res (J).Depth <= N);

            --  Nodes that are not handled yet must have a path smaller than
            --  Max - (N + 1) if they are located before I and smaller than
            --  Max - N otherwise.
            pragma Loop_Invariant
              (for all J in Index_Type =>
                 (if M (J).K and Res (J).Depth > N then
                       Last (M (J).A) < Max - N));
            pragma Loop_Invariant
              (for all J in 1 .. I - 1 =>
                 (if M (J).K and Res (J).Depth > N + 1 then
                       Last (M (J).A) < Max - (N + 1)));

            --  For already handled nodes, the computed Black_Count have the
            --  expected property.
            pragma Loop_Invariant
              (for all J in Index_Type =>
                 (if M (J).K
                  and (Res (J).Depth <= N
                    or (J < I and Res (J).Depth = N + 1)) then
                      Res (J).Status =
                      (Res (Peek (T.Struct, J, Left)).Count
                     = Res (Peek (T.Struct, J, Right)).Count)
                  and Res (J).Depth = 1 + Extended_Index_Type'Max
                      (Res (Peek (T.Struct, J, Left)).Depth,
                       Res (Peek (T.Struct, J, Right)).Depth)
                  and Res (J).Count =
                      (if T.Color (J) = Black then 1 else 0)
                         + Res (Peek (T.Struct, J, Left)).Count));

            --  We have already handled all reachable nodes that have children of
            --  Depth strictly smaller than N, and all reacheable nodes smaller
            --  than I that have children of Depth strictly smaller than N + 1.
            pragma Loop_Invariant
              (for all J in Index_Type =>
                 (if M (J).K
                  and then Res (Peek (T.Struct, J, Left)).Depth < N
                  and then Res (Peek (T.Struct, J, Right)).Depth < N then
                       Res (J).Depth <= N));
            pragma Loop_Invariant
              (for all J in 1 .. I - 1 =>
                 (if M (J).K
                  and then Res (Peek (T.Struct, J, Left)).Depth <= N
                  and then Res (Peek (T.Struct, J, Right)).Depth <= N then
                       Res (J).Depth <= N + 1));

            --  Compute the value of the Black_Count of nodes of Depth N + 1.
            --  Since Depth of nodes are initialized to Max, it is enough to
            --  check that the maximum of the depth of the node children is N
            --  to ensure that its Depth is N + 1.

            if M (I).K then
               declare
                  Count_R : constant Black_Count :=
                    Res (Peek (T.Struct, I, Right));
                  Count_L : constant Black_Count :=
                    Res (Peek (T.Struct, I, Left));
               begin
                  if Index_Type'Max (Count_R.Depth, Count_L.Depth) = N then
                     Res (I).Depth := N + 1;
                     Res (I).Status := (Count_R.Count = Count_L.Count);
                     if T.Color (I) = Black then
                        Res (I).Count := Count_L.Count + 1;
                     else
                        Res (I).Count := Count_L.Count;
                     end if;
                  end if;
               end;
            end if;
         end loop;
      end loop;
      return Res;
   end Nb_Blacks;

   function Same_Nb_Blacks (T : Rbt) return Boolean is
     (Size (T.Struct) = 0 or else
           (for all I in Index_Type =>
                 (if Model (T.Struct) (I).K then
                          Nb_Blacks (T) (I).Status)));
   --  Return True if the number of black nodes is the same in every branch of
   --  the tree.

   procedure Prove_Same_Nb_Blacks (T_Old, T : Rbt) with
   --  Same_Nb_Blacks holds for T_Old and T is T_Old with possibly one or more
   --  additionnal red leafs or a differently colored root.
   --  Prove by induction over the depth of nodes that Same_Nb_Blacks holds for T.

     Ghost,
     Pre => Same_Nb_Blacks (T_Old)
     and then
       (for all I in Index_Type =>
          (if Size (T.Struct) /= 0 and then Model (T.Struct) (I).K
           then (Size (T_Old.Struct) /= 0 and then Model (T_Old.Struct) (I).K)
           or else (Nb_Blacks (T) (I).Status and Nb_Blacks (T) (I).Count = 0)))
     and then Size (T.Struct) >= Size (T_Old.Struct)
     and then
       (for all I in Index_Type =>
          (if Size (T_Old.Struct) /= 0 and then Model (T_Old.Struct) (I).K
           then Model (T.Struct) (I).K))
     and then
       (for all I in Index_Type =>
          (if Size (T_Old.Struct) /= 0 and then
             Model (T_Old.Struct) (I).K and then I /= Root (T.Struct)
           then T_Old.Color (I) = T.Color (I)))
     and then (if Size (T_Old.Struct) /= 0 then Root (T.Struct) = Root (T_Old.Struct))
     and then
       (for all I in Index_Type =>
          (for all D in Direction =>
             (if Size (T_Old.Struct) /= 0 and then Model (T_Old.Struct) (I).K
              then Peek (T_Old.Struct, I, D) = Peek (T.Struct, I, D)
              or else (Peek (T_Old.Struct, I, D) = Empty
                       and then not Model (T_Old.Struct) (Peek (T.Struct, I, D)).K)))),
     Post => Same_Nb_Blacks (T)
   is
   begin
      if Size (T_Old.Struct) > 0 then
         for N in Index_Type loop

            --  For each node that was already in T_Old and which is not the
            --  root, the values of Black_Count are equivalent in T_Old and T.

            pragma Assert
              (for all I in Index_Type =>
                 (for all D in Direction =>
                      (if Model (T_Old.Struct) (I).K
                       and then Nb_Blacks (T_Old) (I).Depth = N - 1
                       then Nb_Blacks (T) (Peek (T.Struct, I, D)).Count =
                         Nb_Blacks (T_Old) (Peek (T_Old.Struct, I, D)).Count)));

            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (T_Old.Struct) (I).K
                    and then Nb_Blacks (T_Old) (I).Depth < N
                    and then I /= Root (T.Struct)
                  then Nb_Blacks (T) (I).Count = Nb_Blacks (T_Old) (I).Count));
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (T_Old.Struct) (I).K
                    and then Nb_Blacks (T_Old) (I).Depth < N
                  then Nb_Blacks (T) (I).Status));
         end loop;
      end if;
   end Prove_Same_Nb_Blacks;

   procedure Prove_Same_Nb_Blacks_Swap
     (T_Old, T : Rbt;
      Except   : Index_Type)
   --  Same_Nb_Blacks holds for T_Old and T is T_Old where Except has been
   --  colored Red (it was black in T_Old) and its children have been colored
   --  Black (they were red in T_Old).
   --  Prove by induction over the depth of nodes that Same_Nb_Blacks holds for T.
   with Ghost,
     Pre  => Same_Nb_Blacks (T_Old)
     and then Size (T.Struct) /= 0 and then Model (T.Struct) (Except).K
     and then Size (T.Struct) = Size (T_Old.Struct)
     and then (for all J in Index_Type =>
                 Model (T.Struct) (J).K = Model (T_Old.Struct) (J).K)
     and then
       (for all I in Index_Type =>
          (for all D in Direction =>
                 (if Model (T.Struct) (I).K
                  then Peek (T_Old.Struct, I, D) = Peek (T.Struct, I, D))))
     and then T.Color (Except) = Red and then T_Old.Color (Except) = Black
     and then
       (for all D in Direction =>
          Peek (T.Struct, Except, D) /= Empty
           and then T.Color (Peek (T.Struct, Except, D)) = Black
           and then T_Old.Color (Peek (T.Struct, Except, D)) = Red)
     and then
       (for all I in Index_Type =>
          (if I not in Except | Peek (T.Struct, Except, Left)
                              | Peek (T.Struct, Except, Right)
           then T.Color (I) = T_Old.Color (I))),
     Post => Same_Nb_Blacks (T)
   is
   begin
      for N in Index_Type loop

         --  For each reachable node, the values of Black_Count are
         --  equivalent in T_Old and T except for children of Except for
         --  which the value of Count has been increased by 1.

         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if Model (T_Old.Struct) (I).K
               and then Nb_Blacks (T_Old) (I).Depth < N
               then
                 (if I in Peek (T.Struct, Except, Left)
                        | Peek (T.Struct, Except, Right)
                  then Nb_Blacks (T) (I).Count = Nb_Blacks (T_Old) (I).Count + 1
                  else Nb_Blacks (T) (I).Count = Nb_Blacks (T_Old) (I).Count)));
         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if Model (T_Old.Struct) (I).K
               and then Nb_Blacks (T_Old) (I).Depth < N
               then Nb_Blacks (T) (I).Status));

         if Nb_Blacks (T_Old) (Except).Depth = N then
            pragma Assert (Nb_Blacks (T) (Except).Status);
            pragma Assert (Nb_Blacks (T) (Except).Count =
                             Nb_Blacks (T_Old) (Except).Count);
         end if;
      end loop;
      pragma Assert
        (for all I in Index_Type =>
           (if Model (T_Old.Struct) (I).K then Nb_Blacks (T) (I).Status));
   end Prove_Same_Nb_Blacks_Swap;

   procedure Prove_Same_Nb_Blacks_Rotate
     (T_Old, T : Rbt;
      X        : Index_Type;
      D1, D2   : Direction)
   --  Same_Nb_Blacks holds for T_Old and T is T_Old rotated around X.
   --  Both X and the child which has taken its place are red.
   --  Prove by induction over the depth of nodes that Same_Nb_Blacks holds for T.

   with Ghost,
     Pre  => Same_Nb_Blacks (T_Old) and then D1 /= D2
     and then Size (T_Old.Struct) /= 0 and then Model (T_Old.Struct) (X).K
     and then Peek (T_Old.Struct, X, D2) /= Empty
     and then Parent (T_Old.Struct, X) /= Empty
     and then Size (T.Struct) = Size (T_Old.Struct)
     and then (for all J in Index_Type =>
                 Model (T.Struct) (J).K = Model (T_Old.Struct) (J).K)
     and then T.Color (X) = Red and then T.Color (Peek (T_Old.Struct, X, D2)) = Red
     and then Peek (T.Struct, X, D2) =
       Peek (T_Old.Struct, Peek (T_Old.Struct, X, D2), D1)
     and then Peek (T.Struct, Parent (T_Old.Struct, X), Position (T_Old.Struct, X)) =
                      Peek (T_Old.Struct, X, D2)
     and then Peek (T.Struct, Peek (T_Old.Struct, X, D2), D1) = X
     and then
       (for all J in Index_Type =>
           (for all D in Direction =>
               (if (J /= X or D = D1)
                 and (J /= Parent (T_Old.Struct, X) or else D /= Position (T_Old.Struct, X))
                 and (J /= Peek (T_Old.Struct, X, D2) or else D = D2)
                 and Model (T.Struct) (J).K
                then Peek (T.Struct, J, D) = Peek (T_Old.Struct, J, D))))
     and then
       (for all I in Index_Type => T.Color (I) = T_Old.Color (I)),
     Post => Same_Nb_Blacks (T)
   is
      Y : constant Index_Type := Peek (T_Old.Struct, X, D2);
   begin
      pragma Assert (Nb_Blacks (T_Old) (X).Count = Nb_Blacks (T_Old) (Y).Count);

      for N in Index_Type loop

         --  For each reachable node, the values of Black_Count are equivalent
         --  in T_Old and T. For the node Y, it cannot be shown at the iteration
         --  corresponding to Y's Depth in T_Old because we need to know that
         --  the invariant holds for X (which is Y's parent in T_Old and Y's
         --  child in T). Therefore, the invariant on Y is delayed until the
         --  iteration corresponding to X's Depth.

         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if Model (T_Old.Struct) (I).K
               and then I /= Y
               and then Nb_Blacks (T_Old) (I).Depth < N
               then Nb_Blacks (T) (I).Count = Nb_Blacks (T_Old) (I).Count));
         pragma Loop_Invariant
           (if Nb_Blacks (T_Old) (X).Depth < N
            then Nb_Blacks (T) (Y).Count = Nb_Blacks (T_Old) (Y).Count);
         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if Model (T_Old.Struct) (I).K
               and then I /= Y
               and then Nb_Blacks (T_Old) (I).Depth < N
               then Nb_Blacks (T) (I).Status));
         pragma Loop_Invariant
           (if Nb_Blacks (T_Old) (X).Depth < N
            then Nb_Blacks (T) (Y).Status);

         if Nb_Blacks (T_Old) (X).Depth = N then
            pragma Assert (Nb_Blacks (T) (X).Status);
            pragma Assert (Nb_Blacks (T) (X).Count = Nb_Blacks (T_Old) (X).Count);
            pragma Assert (Nb_Blacks (T) (Y).Status);
            pragma Assert (Nb_Blacks (T) (Y).Count = Nb_Blacks (T_Old) (Y).Count);
         end if;
         if Nb_Blacks (T_Old) (Parent (T_Old.Struct, X)).Depth = N then
            pragma Assert (Nb_Blacks (T) (Parent (T_Old.Struct, X)).Count =
                             Nb_Blacks (T_Old) (Parent (T_Old.Struct, X)).Count);
         end if;
      end loop;
      pragma Assert
        (for all I in Index_Type =>
           (if Model (T_Old.Struct) (I).K then Nb_Blacks (T) (I).Status));
   end Prove_Same_Nb_Blacks_Rotate;

   procedure Prove_Same_Nb_Blacks_Rotate_Swap
     (T_Old, T : Rbt;
      X        : Index_Type;
      D1, D2   : Direction)
   --  Same_Nb_Blacks holds for T_Old and T is T_Old rotated around X where X
   --  has been colored Red (it was black in T_Old) and the child which has
   --  taken its place has been colored Black (it was red in T_Old).
   --  Prove by induction over the depth of nodes that Same_Nb_Blacks holds for T.

   with Ghost,
     Pre  => Same_Nb_Blacks (T_Old) and then D1 /= D2
     and then Size (T_Old.Struct) /= 0 and then Model (T_Old.Struct) (X).K
     and then Peek (T_Old.Struct, X, D2) /= Empty
     and then Peek (T_Old.Struct, Peek (T_Old.Struct, X, D2), D2) /= Empty
     and then Size (T.Struct) = Size (T_Old.Struct)
     and then (for all J in Index_Type =>
                 Model (T.Struct) (J).K = Model (T_Old.Struct) (J).K)
     and then T_Old.Color (X) = Black
     and then T_Old.Color (Peek (T_Old.Struct, X, D2)) = Red
     and then T_Old.Color (Peek (T_Old.Struct, Peek (T_Old.Struct, X, D2), D2)) = Red
     and then Peek (T.Struct, X, D2) =
       Peek (T_Old.Struct, Peek (T_Old.Struct, X, D2), D1)
     and then (if Parent (T_Old.Struct, X) /= Empty
               then Peek (T.Struct, Parent (T_Old.Struct, X), Position (T_Old.Struct, X)) =
                    Peek (T_Old.Struct, X, D2))
     and then Peek (T.Struct, Peek (T_Old.Struct, X, D2), D1) = X
     and then
       (for all J in Index_Type =>
           (for all D in Direction =>
               (if (J /= X or D = D1)
                 and (J /= Parent (T_Old.Struct, X) or else D /= Position (T_Old.Struct, X))
                 and (J /= Peek (T_Old.Struct, X, D2) or else D = D2)
                 and Model (T.Struct) (J).K
                then Peek (T.Struct, J, D) = Peek (T_Old.Struct, J, D))))
     and then T.Color (X) = Red
     and then T.Color (Peek (T_Old.Struct, X, D2)) = Black
     and then
       (for all I in Index_Type =>
          (if I not in X | Peek (T_Old.Struct, X, D2) then T.Color (I) = T_Old.Color (I))),
     Post => Same_Nb_Blacks (T)
   is
      Y : constant Index_Type := Peek (T_Old.Struct, X, D2);
   begin
      for N in Index_Type loop

         --  For each reachable node, the values of Black_Count are equivalent
         --  in T_Old and T except for X and Y, the Count of X being decreased
         --  by one and the Count of Y being increased by one.
         --  For the node Y, it cannot be shown at the iteration
         --  corresponding to Y's Depth in T_Old because we need to know that
         --  the invariant holds for X (which is Y's parent in T_Old and Y's
         --  child in T). Therefore, the invariant on Y is delayed until the
         --  iteration corresponding to X's Depth.

         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if Model (T_Old.Struct) (I).K
               and then Nb_Blacks (T_Old) (I).Depth < N
               and then I /= Y
               and then I /= X
               then Nb_Blacks (T) (I).Count = Nb_Blacks (T_Old) (I).Count));
         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if Model (T_Old.Struct) (I).K
               and then Nb_Blacks (T_Old) (I).Depth < N
               and then I /= Y
               and then I /= X
               then Nb_Blacks (T) (I).Status));
         pragma Loop_Invariant
           (if Nb_Blacks (T_Old) (X).Depth < N
            then Nb_Blacks (T) (X).Status
            and Nb_Blacks (T) (X).Count = Nb_Blacks (T_Old) (Y).Count
            and Nb_Blacks (T) (Y).Status
            and Nb_Blacks (T) (Y).Count = Nb_Blacks (T_Old) (X).Count);

         if Nb_Blacks (T_Old) (X).Depth = N then
            pragma Assert (Nb_Blacks (T) (X).Status
                           and Nb_Blacks (T) (X).Count = Nb_Blacks (T_Old) (X).Count - 1);
            pragma Assert (Nb_Blacks (T) (Y).Status
                           and Nb_Blacks (T) (Y).Count = Nb_Blacks (T) (X).Count + 1);
         end if;
         if Parent (T_Old.Struct, X) /= Empty
           and then Nb_Blacks (T_Old) (Parent (T_Old.Struct, X)).Depth = N
         then
            pragma Assert (Nb_Blacks (T_Old) (X).Depth < N);
            pragma Assert (Nb_Blacks (T) (Parent (T_Old.Struct, X)).Status
                           and Nb_Blacks (T) (Parent (T_Old.Struct, X)).Count =
                             Nb_Blacks (T) (Parent (T_Old.Struct, X)).Count);
         end if;
      end loop;
      pragma Assert
        (for all I in Index_Type =>
           (if Model (T_Old.Struct) (I).K then Nb_Blacks (T) (I).Status));
   end Prove_Same_Nb_Blacks_Rotate_Swap;


   procedure Insert (T : in out Rbt; V : Natural) is
      X, Y  : Extended_Index_Type;
      T_Old : Rbt := T with Ghost;
      V_Old : Value_Set := Values (T) with Ghost;

   begin
      Insert (T.Struct, V, X);
      if X = Empty then
         Prove_Same_Nb_Blacks (T_Old, T);
         return;
      end if;
      T.Color (X) := Red;
      pragma Assert (Nb_Blacks (T) (X).Status);
      Prove_Same_Nb_Blacks (T_Old, T);
      pragma Assert (Is_Add (V_Old, V, Values (T.Struct)));

      pragma Assert
        (for all I in Index_Type =>
           (if I /= X
            and then
              (Parent (T.Struct, I) = Empty
               or else T.Color (Parent (T.Struct, I)) = Red)
            then T.Color (I) = Black));

      --  X is red, while the parent of X is red, the invariant is broken

      while X /= Root (T.Struct) and then Color (T, Parent (T.Struct, X)) = Red loop
         pragma Loop_Invariant (X /= Empty);
         pragma Loop_Invariant (Size (T.Struct) = Size (T.Struct)'Loop_Entry);
         pragma Loop_Invariant (Root (T.Struct) = Root (T.Struct)'Loop_Entry);
         pragma Loop_Invariant (Model (T.Struct) (X).K);
         pragma Loop_Invariant (Color (T, X) = Red);
         pragma Loop_Invariant (Color (T, Root (T.Struct)) = Black);
         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if I /= X
               and then
                 (Parent (T.Struct, I) = Empty
                  or else T.Color (Parent (T.Struct, I)) = Red)
               then T.Color (I) = Black));
         pragma Loop_Invariant (Values (T.Struct) = Values (T.Struct)'Loop_Entry);
         pragma Loop_Invariant (Same_Nb_Blacks (T));
         T_Old := T;

         if Position (T.Struct, Parent (T.Struct, X)) = Left then

            --  Y is X's uncle

            Y := Peek (T.Struct, Parent (T.Struct, Parent (T.Struct, X)), Right);
            if Color (T, Y) = Red then

               --  If Y is red, move both Y and X's parent to black and the
               --  grand parent to red. This preserves the number of black nodes
               --  per branch.

               T.Color (Y) := Black;
               T.Color (Parent (T.Struct, X)) := Black;
               T.Color (Parent (T.Struct, Y)) := Red;

               --  The grand parent may now break the invariant

               X := Parent (T.Struct, Y);
               Prove_Same_Nb_Blacks_Swap (T_Old, T, X);
            else

               --  Y is black. We will color the grand parent red and rotate it
               --  to the right. To do so, we need the right son of the parent
               --  to be black. If it is X, it is red, so we need to first
               --  rotate it to the left.

               if X = Peek (T.Struct, Parent (T.Struct, X), Right) then
                  X := Parent (T.Struct, X);
                  Left_Rotate (T.Struct, X);
                  Prove_Same_Nb_Blacks_Rotate (T_Old, T, X, Left, Right);
                  T_Old := T;
               end if;

               pragma Assert (Parent (T.Struct, Parent (T.Struct, X)) /= Empty);
               pragma Assert (Peek (T.Struct,
                              Parent (T.Struct, Parent (T.Struct, X)), Left) /= Empty);

               --  Color X's parent black and its grand parent red

               T.Color (Parent (T.Struct, X)) := Black;
               T.Color (Parent (T.Struct, Parent (T.Struct, X))) := Red;
               Right_Rotate (T.Struct, Parent (T.Struct, Parent (T.Struct, X)));
               Prove_Same_Nb_Blacks_Rotate_Swap
                 (T_Old, T, Parent (T_Old.Struct, Parent (T_Old.Struct, X)), Right, Left);

               --  We should now be done

               pragma Assert (Color (T, Parent (T.Struct, X)) = Black);

               pragma Assert
                 (for all I in Index_Type =>
                    (if Parent (T.Struct, I) = Empty
                        or else T.Color (Parent (T.Struct, I)) = Red
                     then T.Color (I) = Black));
               pragma Assert (Is_Add (V_Old, V, Values (T.Struct)));
            end if;
         else

            --  Y is X's uncle

            Y := Peek (T.Struct, Parent (T.Struct, Parent (T.Struct, X)), Left);
            if Color (T, Y) = Red then

               --  If Y is red, move both Y and X's parent to black and the
               --  grand parent to red. This preserves the number of black nodes
               --  per branch.

               T.Color (Y) := Black;
               T.Color (Parent (T.Struct, X)) := Black;
               T.Color (Parent (T.Struct, Y)) := Red;

               --  The grand parent may now break the invariant

               X := Parent (T.Struct, Y);
               Prove_Same_Nb_Blacks_Swap (T_Old, T, X);
            else

               --  Y is black. We will color the grand parent red and rotate it
               --  to the left. To do so, we need the left son of the parent
               --  to be black. If it is X, it is red, so we need to first
               --  rotate it to the right.

               if X = Peek (T.Struct, Parent (T.Struct, X), Left) then
                  X := Parent (T.Struct, X);
                  Right_Rotate (T.Struct, X);
                  Prove_Same_Nb_Blacks_Rotate (T_Old, T, X, Right, Left);
                  T_Old := T;
               end if;

               pragma Assert (Parent (T.Struct, Parent (T.Struct, X)) /= Empty);
               pragma Assert (Peek (T.Struct,
                              Parent (T.Struct, Parent (T.Struct, X)), Right) /= Empty);

               --  Color X's parent black and its grand parent red

               T.Color (Parent (T.Struct, X)) := Black;
               T.Color (Parent (T.Struct, Parent (T.Struct, X))) := Red;
               Left_Rotate (T.Struct, Parent (T.Struct, Parent (T.Struct, X)));
               Prove_Same_Nb_Blacks_Rotate_Swap
                 (T_Old, T, Parent (T_Old.Struct, Parent (T_Old.Struct, X)), Left, Right);

               --  We should now be done

               pragma Assert (Color (T, Parent (T.Struct, X)) = Black);

               pragma Assert
                 (for all I in Index_Type =>
                    (if Parent (T.Struct, I) = Empty
                        or else T.Color (Parent (T.Struct, I)) = Red
                     then T.Color (I) = Black));
               pragma Assert (Is_Add (V_Old, V, Values (T.Struct)));
            end if;
         end if;
      end loop;
      pragma Assert (Is_Add (V_Old, V, Values (T.Struct)));
      pragma Assert
        (for all I in Index_Type =>
           (if I /= Root (T.Struct)
            and then (Parent (T.Struct, I) = Empty
              or else T.Color (Parent (T.Struct, I)) = Red)
            then T.Color (I) = Black));

      --  If we have colored the top red, we can safely color it back to black

      T_Old := T;
      T.Color (Root (T.Struct)) := Black;
      Prove_Same_Nb_Blacks (T_Old, T);
   end Insert;

end Red_Black_Trees;
