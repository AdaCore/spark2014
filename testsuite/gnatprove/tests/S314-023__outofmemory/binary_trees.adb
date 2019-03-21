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

   ---------------
   -- Accessors --
   ---------------

   function Valid_Root (F : Forest; I : Index_Type) return Boolean is
     (I <= F.S and then F.C (I).Position = Top);

   function Size (F : Forest) return Extended_Index_Type is (F.S);

   function Parent (F : Forest; I : Index_Type) return Extended_Index_Type is
     (F.C (I).Parent);

   function Position (F : Forest; I : Index_Type) return Direction is
     (F.C (I).Position);

   function Peek (F : Forest; I : Index_Type; D : Direction) return Extended_Index_Type is
      (if D = Left then F.C (I).Left else F.C (I).Right);

   -----------
   -- Model --
   -----------

   function Model (F : Forest; Root : Index_Type) return Model_Type is
      use I_Set;
      type Boolean_Array is array (Index_Type) of Boolean;

      function Next (ToDo : Boolean_Array) return Extended_Index_Type with
        Post =>
          (if Next'Result = Empty then (for all I in ToDo'Range => not ToDo (I))
           else ToDo (Next'Result))
      is
      begin
         for I in ToDo'Range loop
            pragma Loop_Invariant (for all J in 1 .. I - 1 => not ToDo (J));
            if ToDo (I) then
               return I;
            end if;
         end loop;
         return Empty;
      end Next;

      ToDo   : Boolean_Array := (others => False);
      --  The array containing the nodes that are still to analyze

      Unseen : I_Set.Set := All_Indexes with Ghost;
      --  A set containing all the nodes that have not been analyzed yet. It is
      --  used to ensure termination.

      R      : Model_Type;
      I      : Extended_Index_Type := Root;

   begin
      --  Insert the root in R and store it in the ToDo list

      ToDo (Root) := True;
      R (Root).K := True;

      --  Loop until the ToDo list is empty. Note that we do not prove the
      --  termination of the loop but assume it.

      while I /= Empty loop
         --  Node I is in the ToDo list
         pragma Loop_Invariant (ToDo (I));

         --  All nodes in the ToDo list are in the tree
         pragma Loop_Invariant
           (for all J in Index_Type =>
             (if ToDo (J) then R (J).K));

         --  The path of a node in the ToDo list is maximal wrt other nodes
         --  which are known to be in the tree at this stage.
         pragma Loop_Invariant
           (for all J in Index_Type =>
             (if ToDo (J) then
               (for all K in Index_Type =>
                  (if R (K).K then not (R (J).A < R (K).A)))));

         --  The root is in tree with an empty path
         pragma Loop_Invariant (R (Root).K and Length (R (Root).A) = 0);

         --  Non-root nodes are in the tree iff their parent is in the tree
         pragma Loop_Invariant
           (for all J in Index_Type =>
             (if R (J).K and J /= Root then F.C (J).Parent /= Empty
              and then R (F.C (J).Parent).K));

         --  The path from the root to non-root tree nodes is equal to the path
         --  to their parent extended by the last direction to get to the node.
         --  For other nodes, the path is empty.
         pragma Loop_Invariant
           (for all J in Index_Type =>
             (if R (J).K and J /= Root
              then Is_Add (R (F.C (J).Parent).A, F.C (J).Position, R (J).A)
              else Length (R (J).A) = 0));

         --  A node known to be in the tree is either the root node, or a node
         --  whose parent is known to be in the tree. In that case, the node is
         --  either known to be in the tree, or the parent is still in the ToDo
         --  list.
         pragma Loop_Invariant
           (for all J in Index_Type =>
             (if J /= Root then
               (if F.C (J).Parent /= Empty and then R (F.C (J).Parent).K
                then R (J).K or ToDo (F.C (J).Parent)
                else not R (J).K)));

         --  A node known to be in the tree does not have its parent in the ToDo
         --  list.
         pragma Loop_Invariant
           (for all J in Index_Type =>
             (if R (J).K and then J /= Root then not ToDo (F.C (J).Parent)));

         --  Nodes in the tree all have different associated paths
         pragma Loop_Invariant
           (for all J in Index_Type =>
             (if R (J).K then
               (for all K in Index_Type =>
                 (if R (K).K and R (K).A = R (J).A
                  then J = K))));

         --  The root is part of the tree, and the path from the root to itself
         --  is empty.
         pragma Loop_Invariant (R (Root).K and Length (R (Root).A) = 0);

         --  The longest path stored so far is of size Max - Length (Unseen) at
         --  most.
         pragma Loop_Invariant
           (for all J in Index_Type =>
              Length (R (J).A) <= Max - Length (Unseen));

         --  Nodes that have not been handled yet are either not in the tree or
         --  in the ToDo list.
         pragma Loop_Invariant
           (for all J in Index_Type =>
              (Contains (Unseen, J) = (not R (J).K or ToDo (J))));

         --  At each iteration of the loop, we add a new node in the tree
         pragma Loop_Variant (Decreases => Length (Unseen));

         --  Remove I from the set of unseen nodes
         Unseen := Remove (Unseen, I);

         declare
            J : Extended_Index_Type;
         begin
            --  Update model R for the left child. Add it to the ToDo list.
            J := F.C (I).Left;
            if J /= Empty then
               pragma Assert (Length (Unseen) > 0);
               R (J).K  := True;
               R (J).A  := Add (R (F.C (J).Parent).A, Left);
               ToDo (J) := True;
            end if;

            --  Update model R for the right child. Add it to the ToDo list.
            J := F.C (I).Right;
            if J /= Empty then
               pragma Assert (Length (Unseen) > 0);
               R (J).K  := True;
               R (J).A  := Add (R (F.C (J).Parent).A, Right);
               ToDo (J) := True;
            end if;
         end;

         --  Nothing more to do for node I
         ToDo (I) := False;
         I := Next (ToDo);
      end loop;

      --  Restate part of the loop invariant after the last iteration of the
      --  loop.
      pragma Assert
        (for all J in Index_Type =>
          (if J /= Root then
            (if F.C (J).Parent /= Empty and then R (F.C (J).Parent).K
             then R (J).K or ToDo (F.C (J).Parent)
             else not R (J).K)));

      return R;
   end Model;

   --------------------------
   -- Prove_Model_Distinct --
   --------------------------

   procedure Prove_Model_Distinct (F : Forest; T1, T2 : Index_Type) is
   begin
      for N in Index_Type loop
         pragma Loop_Invariant
           (for all I in Index_Type =>
             (if Model (F, T1) (I).K and Length (Model (F, T1) (I).A) < N
              then not Model (F, T2) (I).K));
      end loop;
   end Prove_Model_Distinct;

   ---------------------------
   -- Prove_Model_Preserved --
   ---------------------------

   --  State that the model is preserved for a tree in forest F1 when looking at
   --  the exact same tree unmodified in a forest F2, which is an extension of
   --  F1 where possibly other trees have been modified.

   procedure Prove_Model_Preserved (F1, F2 : Forest; Root : Index_Type) with
     Ghost,
     Global => null,
     Pre  =>
       --  F1 and F2 respect the invariant of forests
       Tree_Structure (F1)
       and then Tree_Structure (F2)

       --  Root is a root of F1
       and then F1.C (Root).Position = Top
       and then Root in 1 .. F1.S

       --  F2 is larger than F1
       and then F2.S >= F1.S

       --  All the nodes in the tree rooted at Root in F1 are identical in F2
       and then (for all I in Index_Type =>
                  (if Model (F1, Root) (I).K then F1.C (I) = F2.C (I))),
     Post =>
       --  Root is a root of F2
       F2.C (Root).Position = Top

       --  F1 and F2 have the same model tree
       and then Model (F1, Root) = Model (F2, Root)
   is
   begin
      for N in Index_Type loop

         --  Nodes from F1 which are less than N links away from the root are
         --  also in the tree rooted at Root in F2.
         pragma Loop_Invariant
           (for all I in Index_Type =>
             (if Model (F1, Root) (I).K and Length (Model (F1, Root) (I).A) < N then
                Model (F2, Root) (I).K));

         --  Nodes from F1 which are less than N links away from the root have
         --  the same path in F1 and F2.
         pragma Loop_Invariant
           (for all I in Index_Type =>
             (if Model (F1, Root) (I).K and Length (Model (F1, Root) (I).A) < N then
                Model (F2, Root) (I).A = Model (F1, Root) (I).A));

         --  Nodes from F2 which are less than N links away from the root are
         --  also in the tree rooted at Root in F1.
         pragma Loop_Invariant
           (for all I in Index_Type =>
             (if Model (F2, Root) (I).K and Length (Model (F2, Root) (I).A) < N then
                Model (F1, Root) (I).K));

         --  Nodes that are exactly N links away from the root have the same
         --  path in F1 and F2.
         for J in Index_Type loop

            --  Use Preserve_Equal to prove the property for node J, based on
            --  the knowledge that it holds for the parent of node J.

            if Model (F1, Root) (J).K and Length (Model (F1, Root) (J).A) = N then
               Preserve_Equal (S1 => Model (F1, Root) (F1.C (J).Parent).A,
                               S2 => Model (F2, Root) (F1.C (J).Parent).A,
                               S3 => Model (F1, Root) (J).A,
                               S4 => Model (F2, Root) (J).A,
                               D  => F1.C (J).Position);
            end if;

            --  Accumulate the knowledge that the property holds up to node J

            pragma Loop_Invariant
              (for all I in 1 .. J =>
                (if Model (F1, Root) (I).K and Length (Model (F1, Root) (I).A) = N then
                   Model (F2, Root) (I).A = Model (F1, Root) (I).A));
         end loop;
      end loop;
   end Prove_Model_Preserved;

   -----------------------
   -- Prove_Model_Total --
   -----------------------

   --  State first a local ghost lemma to prove the property expressed in
   --  Prove_Model_Total for all values of node I and direction D. Then use
   --  that lemma in the version of Prove_Model_Total for a specific I and D.

   procedure Prove_Model_Total (F : Forest; Root : Index_Type) with
     Ghost,
     Global => null,
     Pre  => Tree_Structure (F)
       and then Valid_Root (F, Root),
     Post =>
       (for all I in Index_Type =>
         (if Model (F, Root) (I).K then
           (for all D in Direction =>
             (if Peek (F, I, D) = Empty then
               (for all J in Index_Type =>
                 (if Model (F, Root) (J).K
                    and then (Model (F, Root) (I).A < Model (F, Root) (J).A)
                  then Get (Model (F, Root) (J).A, Length (Model (F, Root) (I).A) + 1) /= D))))))
   is
   begin
      for N in Index_Type loop
         pragma Loop_Invariant
           (for all I in Index_Type =>
             (if Model (F, Root) (I).K then
               (for all D in Direction =>
                 (if Peek (F, I, D) = Empty then
                   (for all J in Index_Type =>
                     (if Model (F, Root) (J).K
                        and then Model (F, Root) (I).A < Model (F, Root) (J).A
                        and then Length (Model (F, Root) (J).A) <= Length (Model (F, Root) (I).A) + N
                      then Get (Model (F, Root) (J).A, Length (Model (F, Root) (I).A) + 1) /= D))))));
      end loop;
   end Prove_Model_Total;

   procedure Prove_Model_Total (F : Forest; Root, I : Index_Type; D : Direction) is
   begin
      Prove_Model_Total (F, Root);
   end Prove_Model_Total;

   -------------
   -- Extract --
   -------------

   procedure Extract (F : in out Forest; Root, I : Index_Type; D : Direction; V : out Extended_Index_Type) is

      --  Save a copy of the forest on entry for use in assertions
      F_Old : Forest := F with Ghost;

      --  The proof of the postcondition of Extract is isolated in a local ghost
      --  lemma Prove_Post.

      procedure Prove_Post with
        Ghost,
        Global => (Input => (F, Root, V, F_Old)),
        Pre  =>
          --  The size of the forest does not change
          F.S = F_Old.S

          --  Root was the root of a tree
          and then Root <= F.S
          and then F_Old.C (Root).Position = Top

          --  Root and V are different nodes
          and then V /= Root

          --  V is the root of a tree
          and then V in 1 .. F.S
          and then F.C (V).Position = Top

          --  V was in the tree
          and then Model (F_Old, Root) (V).K

          --  Except for V, the value of parent link is preserved
          and then (for all I in Index_Type =>
                     (if I /= V then F.C (I).Parent = F_Old.C (I).Parent))

          --  Except for V, the value of position is preserved
          and then (for all I in Index_Type =>
                     (if I /= V then  F.C (I).Position = F_Old.C (I).Position))

          --  For nodes previously not in the tree, the value of left child is
          --  preserved.
          and then (for all J in Index_Type =>
                     (if not Model (F_Old, Root) (J).K then
                        F.C (J).Left = F_Old.C (J).Left))

          --  For nodes previously not in the tree, the value of right child is
          --  preserved.
          and then (for all J in Index_Type =>
                     (if not Model (F_Old, Root) (J).K then
                        F.C (J).Right = F_Old.C (J).Right)),
        Post =>
          --  Nodes previously in the tree rooted at Root either remain nodes in
          --  the tree rooted at Root, or for those nodes which have V on their
          --  path, become nodes in the tree rooted at V.
          (for all I in Index_Type =>
            (if Model (F_Old, Root) (I).K then
              (if Model (F_Old, Root) (V).A <= Model (F_Old, Root) (I).A
               then Model (F, V) (I).K
               else Model (F, Root) (I).K)))

          --  Nodes in the tree rooted at Root were previously in the tree
          --  rooted at Root.
          and then (for all I in Index_Type =>
                     (if Model (F, Root) (I).K then Model (F_Old, Root) (I).K))

          --  Nodes in the tree rooted at V were previously in the tree rooted
          --  at Root.
          and then (for all I in Index_Type =>
                     (if Model (F, V) (I).K then Model (F_Old, Root) (I).K))

          --  Paths are preserved for nodes in the tree rooted at Root
          and then (for all I in Index_Type =>
                     (if Model (F, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A))


          --  The path for nodes in the tree rooted at V is obtained by
          --  subtracting the path from Root to V from the path from Root to
          --  the node.
          and then (for all I in Index_Type =>
                     (if Model (F, V) (I).K then
                        Is_Concat (Q => Model (F_Old, Root) (V).A,
                                   V => Model (F, V) (I).A,
                                   P => Model (F_Old, Root) (I).A)))

          --  All other trees in the forest are preserved
          and then (for all R in 1 .. F.S =>
                     (if R /= Root and R /= V and F_Old.C (R).Position = Top then
                        Model (F_Old, R) = Model (F, R)))
      is
      begin
         pragma Assert (F.C (Root).Position = Top);
         pragma Assert
           (for all I in Index_Type =>
             (if F.C (I).Parent > Empty and then Model (F, V) (F.C (I).Parent).K
              then I /= V and then Model (F, V) (I).K));
         pragma Assert (not (Model (F, Root) (V).K));
         for N in Index_Type loop

            --  Nodes from F_Old which are less than N links away from the root
            --  either remain nodes in the tree rooted at Root, or for those
            --  nodes which have V on their path, become nodes in the tree
            --  rooted at V.
            pragma Loop_Invariant
              (for all I in Index_Type =>
                (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N - 1 then
                  (if Model (F_Old, Root) (V).A <= Model (F_Old, Root) (I).A
                   then Model (F, V) (I).K
                   else Model (F, Root) (I).K)));

            --  Nodes which are less than N links away from the root Root were
            --  previously in the tree rooted at Root.
            pragma Loop_Invariant
              (for all I in Index_Type =>
                (if Model (F, Root) (I).K and then Length (Model (F, Root) (I).A) <= N - 1
                 then Model (F_Old, Root) (I).K));

            --  Nodes which are less than N links away from the root V were
            --  previously in the tree rooted at Root.
            pragma Loop_Invariant
              (for all I in Index_Type =>
                (if Model (F, V) (I).K and then Length (Model (F, V) (I).A) <= N - 1
                 then Model (F_Old, Root) (I).K));

            --  Nodes from F_Old which are less than N links away from the root
            --  and still in the tree rooted at Root have the same path in F_Old
            --  and F.
            pragma Loop_Invariant
              (for all I in Index_Type =>
                (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N - 1 then
                  (if Model (F, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A)));

            --  Nodes from F_Old which are less than N links away from the
            --  root and now in the tree rooted at V have a path obtained by
            --  subtracting the path from Root to V from the path from Root
            --  to the node.
            pragma Loop_Invariant
              (for all I in Index_Type =>
                (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N - 1 then
                  (if Model (F, V) (I).K then
                     Is_Concat (Q => Model (F_Old, Root) (V).A,
                                V => Model (F, V) (I).A,
                                P => Model (F_Old, Root) (I).A))));

            --  Nodes that are exactly N links away from the root have the same
            --  path in F_Old and F, or for those nodes for which V is on the
            --  path, their path is obtained by subtracting the path from
            --  Root to V from the path from Root to the node.
            for KI in Index_Type loop

               --  Case 1: node KI is in the tree rooted at Root in F. Use
               --  Preserve_Equal to prove the property for node KI, based
               --  on the knowledge that it holds for the parent of node KI.

               if Model (F_Old, Root) (KI).K
                 and then Length (Model (F_Old, Root) (KI).A) = N
                 and then Model (F, Root) (KI).K
               then
                  Preserve_Equal (S1 => Model (F, Root) (F.C (KI).Parent).A,
                                  S2 => Model (F_Old, Root) (F.C (KI).Parent).A,
                                  S3 => Model (F, Root) (KI).A,
                                  S4 => Model (F_Old, Root) (KI).A,
                                  D  => F.C (KI).Position);
               end if;

               --  Case 2: node KI is in the tree rooted at V in F. Use
               --  Preserve_Concat to prove the property for node KI, based
               --  on the knowledge that it holds for the parent of node KI.

               if Model (F_Old, Root) (KI).K
                 and then Length (Model (F_Old, Root) (KI).A) = N
                 and then Model (F, V) (KI).K
                 and then KI /= V
               then
                  Preserve_Concat (S1 => Model (F, V) (F.C (KI).Parent).A,
                                   S2 => Model (F_Old, Root) (F.C (KI).Parent).A,
                                   S3 => Model (F, V) (KI).A,
                                   S4 => Model (F_Old, Root) (KI).A,
                                   T  => Model (F_Old, Root) (V).A,
                                   D  => F.C (KI).Position);
               end if;

               --  Accumulate the knowledge that the property holds up to node
               --  KI.

               pragma Loop_Invariant
                 (for all I in 1 .. KI =>
                   (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N then
                     (if Model (F, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A)));
               pragma Loop_Invariant
                 (for all I in 1 .. KI =>
                   (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N then
                     (if Model (F, V) (I).K then
                        Is_Concat (Q => Model (F_Old, Root) (V).A,
                                   V => Model (F, V) (I).A,
                                   P => Model (F_Old, Root) (I).A))));
            end loop;
         end loop;

         for R in 1 .. F_Old.S loop
            if R /= Root and R /= V and F_Old.C (R).Position = Top then
               Prove_Model_Distinct (F_Old, Root, R);
               Prove_Model_Preserved (F_Old, F, R);
            end if;
            pragma Loop_Invariant
              (for all P in 1 .. R =>
                 (if P /= Root and P /= V and F_Old.C (P).Position = Top then
                       Model (F_Old, P) = Model (F, P)));
         end loop;
      end Prove_Post;

   begin
      V := (if D = Left then F.C (I).Left else F.C (I).Right);

      if V /= Empty then
         if D = Left then
            F.C (I).Left := Empty;
         else
            F.C (I).Right := Empty;
         end if;
         pragma Assert (F.C (V).Parent = I);
         F.C (V).Position := Top;
         F.C (V).Parent := Empty;
      end if;

      pragma Assert
        (for all I in Index_Type =>
          (if F.C (I).Parent /= Empty and then F.C (I).Position = Left
           then F.C (F.C (I).Parent).Left = I));
      pragma Assert
        (for all I in Index_Type =>
          (if F.C (I).Parent /= Empty and then F.C (I).Position = Right
           then F.C (F.C (I).Parent).Right = I));

      if V /= Empty then
         Prove_Post;
      end if;
   end Extract;

   ----------
   -- Plug --
   ----------

   procedure Plug (F       : in out Forest;
                   Root, I : Index_Type;
                   D       : Direction;
                   V       : Extended_Index_Type)
   is
      --  Save a copy of the forest on entry for use in assertions
      F_Old : Forest := F with Ghost;

      --  The proof of the postcondition of Plug is isolated in a local ghost
      --  lemma Prove_Post.

      procedure Prove_Post with
        Ghost,
        Global => (Input => (F, Root, V, F_Old)),
        Pre  =>
          --  The size of the forest does not change
          F.S = F_Old.S

          --  Root was and is still the root of a tree
          and then Root <= F.S
          and then F_Old.C (Root).Position = Top
          and then F.C (Root).Position = Top

          --  Root and V are different nodes
          and then V /= Root

          --  V was the root of a tree
          and then V in 1 .. F.S
          and then F_Old.C (V).Position = Top

          --  V has a parent which was previously in the tree
          and then F.C (V).Parent /= Empty
          and then Model (F_Old, Root) (F.C (V).Parent).K

          --  Except for V, the value of parent link is preserved
          and then (for all I in Index_Type =>
                     (if I /= V then F.C (I).Parent = F_Old.C (I).Parent))

          --  Except for V, the value of position is preserved
          and then (for all I in Index_Type =>
                     (if I /= V then  F.C (I).Position = F_Old.C (I).Position))

          --  For nodes previously not in the tree, the value of left child is
          --  preserved.
          and then (for all J in Index_Type =>
                     (if not Model (F_Old, Root) (J).K then
                        F.C (J).Left = F_Old.C (J).Left))

          --  For nodes previously not in the tree, the value of right child is
          --  preserved.
          and then (for all J in Index_Type =>
                     (if not Model (F_Old, Root) (J).K then
                        F.C (J).Right = F_Old.C (J).Right)),
        Post =>
          --  V is in the tree
          Model (F, Root) (V).K

          --  Nodes in the tree rooted at Root come either from the tree
          --  previously rooted at Root, or for those nodes which have V
          --  on their path, from the tree previously rooted at V.
          and then (for all I in Index_Type =>
                     (if Model (F, Root) (I).K then
                       (if Model (F, Root) (V).A <= Model (F, Root) (I).A
                        then Model (F_Old, V) (I).K
                        else Model (F_Old, Root) (I).K)))

          --  Nodes previously in the tree are still in the tree
          and then (for all I in Index_Type =>
                     (if Model (F_Old, Root) (I).K then Model (F, Root) (I).K))

          and then (for all I in Index_Type =>
                     (if Model (F_Old, V) (I).K then Model (F, Root) (I).K))

          --  Paths are preserved for nodes that were previously in the tree
          and then (for all I in Index_Type =>
                     (if Model (F_Old, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A))

          --  The path for nodes in the tree previously rooted at V is obtained
          --  by concatenating the path from Root to V and the path from V to
          --  the node.
          and then (for all I in Index_Type =>
                     (if Model (F_Old, V) (I).K then
                        Is_Concat (Q => Model (F, Root) (V).A,
                                   V => Model (F_Old, V) (I).A,
                                   P => Model (F, Root) (I).A)))

          --  All other trees in the forest are preserved
          and then (for all R in 1 .. F.S =>
                     (if R /= Root and R /= V and F_Old.C (R).Position = Top then
                        Model (F_Old, R) = Model (F, R)))
      is
      begin
         pragma Assert
           (for all I in Index_Type =>
             (if Model (F, Root) (I).K
                and then Model (F, Root) (V).A <= Model (F, Root) (I).A
                and then F.C (I).Parent /= Empty
              then I = V
                or else Model (F, Root) (V).A <= Model (F, Root) (F.C (I).Parent).A));
         for N in Index_Type loop
            pragma Loop_Invariant
              (for all I in Index_Type =>
                (if Length (Model (F, Root) (V).A) > 0
                   and then Model (F, Root) (I).K
                   and then Length (Model (F, Root) (I).A) <= N - 1
                 then
                   (if Model (F, Root) (V).A <= Model (F, Root) (I).A
                    then Model (F_Old, V) (I).K
                    else Model (F_Old, Root) (I).K)));

            --  Nodes from F_Old which are less than N links away from the root
            --  are also in the tree rooted at Root in F.
            pragma Loop_Invariant
              (for all I in Index_Type =>
                (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N - 1
                 then Model (F, Root) (I).K));

            --  Nodes from F_Old which are less than N links away from V and
            --  whose parent is in the tree are also in the tree rooted at
            --  Root in F.
            pragma Loop_Invariant
              (for all I in Index_Type =>
                (if Model (F_Old, V) (I).K
                   and then Length (Model (F_Old, V) (I).A) <= N - 1
                   and then Model (F, Root) (F.C (V).Parent).K
                 then Model (F, Root) (I).K));

            --  Nodes from F which are less than N links away from the root and
            --  are also in the tree rooted at Root in F_Old have the same path
            --  in F_Old and F.
            pragma Loop_Invariant
              (for all I in Index_Type =>
                (if Model (F, Root) (I).K and then Length (Model (F, Root) (I).A) <= N - 1 then
                  (if Model (F_Old, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A)));

            --  Nodes from F which are less than N links away from the root
            --  and are also in the tree rooted at V in F_Old have a path in F
            --  obtained by concatenating the path from Root to V and the path
            --  from V to the node.
            pragma Loop_Invariant
              (for all I in Index_Type =>
                (if Model (F, Root) (I).K and then Length (Model (F, Root) (I).A) <= N - 1 then
                  (if Model (F_Old, V) (I).K then
                     Is_Concat (Q => Model (F, Root) (V).A,
                                V => Model (F_Old, V) (I).A,
                                P => Model (F, Root) (I).A))));

            --  Nodes that are exactly N links away from the root have the same
            --  path in F_Old and F, or for those nodes for which V is on the
            --  path, their path is obtained by concatenating the path from
            --  Root to V and the path from V to the node.
            for KI in Index_Type loop

               --  Case 1: node KI is in the tree rooted at Root in F_Old. Use
               --  Preserve_Equal to prove the property for node KI, based on
               --  the knowledge that it holds for the parent of node KI.

               if Model (F, Root) (KI).K
                 and then Length (Model (F, Root) (KI).A) = N
                 and then Model (F_Old, Root) (KI).K
               then
                  Preserve_Equal (S1 => Model (F, Root) (F.C (KI).Parent).A,
                                  S2 => Model (F_Old, Root) (F.C (KI).Parent).A,
                                  S3 => Model (F, Root) (KI).A,
                                  S4 => Model (F_Old, Root) (KI).A,
                                  D  => F.C (KI).Position);
               end if;

               --  Case 2: node KI is in the tree rooted at V in F_Old. Use
               --  Preserve_Concat to prove the property for node KI, based
               --  on the knowledge that it holds for the parent of node KI.

               if Model (F, Root) (KI).K
                 and then Length (Model (F, Root) (KI).A) = N
                 and then Model (F_Old, V) (KI).K
                 and then KI /= V
               then
                  Preserve_Concat (S1 => Model (F_Old, V) (F.C (KI).Parent).A,
                                   S2 => Model (F, Root) (F.C (KI).Parent).A,
                                   S3 => Model (F_Old, V) (KI).A,
                                   S4 => Model (F, Root) (KI).A,
                                   T  => Model (F, Root) (V).A,
                                   D  => F.C (KI).Position);
               end if;

               --  Accumulate the knowledge that the property holds up to node
               --  KI.

               pragma Loop_Invariant
                 (for all I in 1 .. KI =>
                   (if Model (F, Root) (I).K and then Length (Model (F, Root) (I).A) <= N then
                     (if Model (F_Old, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A)));
               pragma Loop_Invariant
                 (for all I in 1 .. KI =>
                   (if Model (F, Root) (I).K and then Length (Model (F, Root) (I).A) <= N then
                     (if Model (F_Old, V) (I).K then
                        Is_Concat (Q => Model (F, Root) (V).A,
                                   V => Model (F_Old, V) (I).A,
                                   P => Model (F, Root) (I).A))));
            end loop;
         end loop;
         pragma Assert
           (for all I in Index_Type =>
             (if Model (F_Old, V) (I).K then Model (F, Root) (I).K));
         pragma Assert
           (for all I in Index_Type =>
             (if Model (F, Root) (I).K then
               (if Model (F, Root) (V).A <= Model (F, Root) (I).A
                then Model (F_Old, V) (I).K
                else Model (F_Old, Root) (I).K)));

         --  All other trees in the forest are preserved
         for R in 1 .. F_Old.S loop

            --  Use Prove_Model_Distinct to prove that a different tree rooted
            --  in R shared no nodes with the trees rooted in Root and V. Then
            --  use Prove_Model_Preserved to prove that the tree rooted in R has
            --  been preserved.

            if R /= Root and R /= V and F_Old.C (R).Position = Top then
               Prove_Model_Distinct (F_Old, Root, R);
               Prove_Model_Distinct (F_Old, V, R);
               Prove_Model_Preserved (F_Old, F, R);
            end if;

            --  Accumulate the knowledge that the property holds up to node R

            pragma Loop_Invariant
              (for all P in 1 .. R =>
                (if P /= Root and P /= V and F_Old.C (P).Position = Top then
                   Model (F, P) = Model (F_Old, P)));
         end loop;
      end Prove_Post;

   begin
      if V /= Empty then
         if D = Left then
            F.C (I).Left := V;
         else
            F.C (I).Right := V;
         end if;
         F.C (V).Position := D;
         F.C (V).Parent := I;

         Prove_Post;
      end if;
   end Plug;

   ------------
   -- Insert --
   ------------

   procedure Insert (F       : in out Forest;
                     Root, I : Index_Type;
                     D       : Direction;
                     V       : out Index_Type)
   is
      --  Save a copy of the forest on entry for use in assertions
      F_Old : Forest := F with Ghost;

      --  The proof of the postcondition of Insert is isolated in a local ghost
      --  lemma Prove_Post.

      procedure Prove_Post with
        Ghost,
        Global => (Input => (F, Root, V, F_Old)),
        Pre  =>
          --  Root is the root of a tree
          F_Old.C (Root).Position = Top
          and then Root in 1 .. F_Old.S

          --  V is a valid node
          and then V /= Empty

          --  Size of tree is increasing
          and then F.S >= F_Old.S

          --  V was not in the tree previously
          and then not Model (F_Old, Root) (V).K

          --  V has a parent which was previously in the tree
          and then F.C (V).Parent /= Empty
          and then Model (F_Old, Root) (F.C (V).Parent).K

          --  V has no children
          and then F.C (V).Left = Empty
          and then F.C (V).Right = Empty

          --  Except for V, the value of parent link is preserved
          and then (for all I in Index_Type =>
                     (if I /= V
                      then F.C (I).Parent = F_Old.C (I).Parent))

          --  Except for V, the value of position is preserved
          and then (for all I in Index_Type =>
                     (if I /= V
                      then F.C (I).Position = F_Old.C (I).Position))

          --  For nodes previously not in the tree, the value of left child is
          --  preserved.
          and then (for all J in Index_Type =>
                     (if not Model (F_Old, Root) (J).K
                      then F.C (J).Left = F_Old.C (J).Left))

          --  For nodes previously not in the tree, the value of right child is
          --  preserved.
          and then (for all J in Index_Type =>
                     (if not Model (F_Old, Root) (J).K
                      then F.C (J).Right = F_Old.C (J).Right)),
        Post =>
          --  Nodes previously in the tree are still in the tree
          (for all I in Index_Type =>
             (if Model (F_Old, Root) (I).K then Model (F, Root) (I).K))

          --  V is in the tree
          and then Model (F, Root) (V).K

          --  Nodes that are in the tree consist in nodes previously in the tree
          --  plus the new node V.
          and then (for all I in Index_Type =>
                     (if Model (F, Root) (I).K and I /= V then Model (F_Old, Root) (I).K))

          --  Paths are preserved for nodes that were previously in the tree
          and then (for all I in Index_Type =>
                     (if Model (F_Old, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A))

          --  All other trees in the forest are preserved
          and then (for all R in 1 .. F_Old.S =>
                     (if R /= Root and F_Old.C (R).Position = Top and R /= V then  --  ??? Why R /= V
                        Model (F_Old, R) = Model (F, R)))
      is
      begin
         for N in Index_Type loop

            --  Nodes from F_Old which are less than N links away from the root
            --  are also in the tree rooted at Root in F.
            pragma Loop_Invariant
              (for all I in Index_Type =>
                (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) < N
                 then Model (F, Root) (I).K));

            --  Nodes from F_Old which are less than N links away from the root
            --  have the same path in F_Old and F.
            pragma Loop_Invariant
              (for all I in Index_Type =>
                (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) < N
                 then Model (F, Root) (I).A = Model (F_Old, Root) (I).A));

            --  Except from V, nodes from F which are less than N links away
            --  from the root are also in the tree rooted at Root in F_Old.
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F, Root) (I).K
                    and then Length (Model (F, Root) (I).A) < N
                    and then I /= V
                  then Model (F_Old, Root) (I).K));

            --  Nodes that are exactly N links away from the root have the same
            --  path in F_Old and F.
            for KI in Index_Type loop

               --  Use Preserve_Equal to prove the property for node KI, based
               --  on the knowledge that it holds for the parent of node KI.

               if Model (F_Old, Root) (KI).K and then Length (Model (F_Old, Root) (KI).A) = N then
                  Preserve_Equal (S1 => Model (F, Root) (F.C (KI).Parent).A,
                                  S2 => Model (F_Old, Root) (F.C (KI).Parent).A,
                                  S3 => Model (F, Root) (KI).A,
                                  S4 => Model (F_Old, Root) (KI).A,
                                  D  => F.C (KI).Position);
               end if;

               --  Accumulate the knowledge that the property holds up to node
               --  KI.

               pragma Loop_Invariant
                 (for all I in 1 .. KI =>
                   (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N then
                      Model (F, Root) (I).A = Model (F_Old, Root) (I).A));
            end loop;
         end loop;

         --  All other trees in the forest are preserved
         for R in 1 .. F_Old.S loop

            --  Use Prove_Model_Distinct to prove that a different tree rooted
            --  in R shared no nodes with the tree rooted in Root. Then use
            --  Prove_Model_Preserved to prove that the tree rooted in R has
            --  been preserved.

            if R /= Root and F_Old.C (R).Position = Top and R /= V then
               Prove_Model_Distinct (F_Old, Root, R);
               Prove_Model_Preserved (F_Old, F, R);
            end if;

            --  Accumulate the knowledge that the property holds up to node R

            pragma Loop_Invariant
              (for all P in 1 .. R =>
                (if P /= Root and F_Old.C (P).Position = Top and P /= V then
                   Model (F_Old, P) = Model (F, P)));
         end loop;
      end Prove_Post;

   begin
      V := F.S + 1;

      --  Plug it as the D child of I

      F.C (V).Position := D;
      F.C (V).Parent := I;

      if D = Left then
         F.C (I).Left := V;
      else
         F.C (I).Right := V;
      end if;

      F.S := F.S + 1;

      pragma Assert
        (for all I in Index_Type =>
             (if F.C (I).Parent /= Empty and then F.C (I).Position = Left
              then F.C (F.C (I).Parent).Left = I));
      pragma Assert
        (for all I in Index_Type =>
             (if F.C (I).Parent /= Empty and then F.C (I).Position = Right
              then F.C (F.C (I).Parent).Right = I));
      Prove_Post;
   end Insert;

   ----------
   -- Init --
   ----------

   procedure Init (F : in out Forest; Root : out Index_Type) is

      --  Save a copy of the forest on entry for use in assertions
      F_Old : Forest := F with Ghost;

      --  The proof of the postcondition of Init is isolated in a local ghost
      --  lemma Prove_Post.

      procedure Prove_Post with
        Ghost,
        Global => (Input    => (F, F_Old),
                   Proof_In => Root),
        Pre  =>
          --  Root was previously not allocated, and it is allocated now
          Root in F_Old.S + 1 .. F.S

          --  Values of parent/position/left/right are preserved for all nodes
          and then (for all I in Index_Type => F.C (I).Parent = F_Old.C (I).Parent)
          and then (for all I in Index_Type => F.C (I).Position = F_Old.C (I).Position)
          and then (for all I in Index_Type => F.C (I).Left = F_Old.C (I).Left)
          and then (for all I in Index_Type => F.C (I).Right = F_Old.C (I).Right),
        Post =>
          --  All trees that were previously allocated are preserved
          (for all R in 1 .. F_Old.S =>
            (if F_Old.C (R).Position = Top then
               Model (F_Old, R) = Model (F, R)))

          --  The only node in the tree rooted at Root is Root itself
          and then (for all I in Index_Type =>
                     (if I /= Root then not Model (F, Root) (I).K))
      is
      begin
         --  For a node different from Root to be in the new tree, it would
         --  need to have a path length from Root that is greater than Max. This
         --  leads to a contradiction, which allows to get the property that the
         --  only node in the tree rooted at Root is Root itself.

         for N in Extended_Index_Type loop
            pragma Loop_Invariant
              (for all J in Index_Type =>
                (if Model (F, Root) (J).K and then J /= Root
                 then Length (Model (F, Root) (J).A) > N));
         end loop;

         --  All trees that were previously allocated are preserved
         for R in 1 .. F_Old.S loop

            --  Use Prove_Model_Preserved to prove the property for node R

            if F_Old.C (R).Position = Top then
               Prove_Model_Preserved (F_Old, F, R);
            end if;

            --  Accumulate the knowledge that the property holds up to node R

            pragma Loop_Invariant
              (for all P in 1 .. R =>
                (if F_Old.C (P).Position = Top then Model (F_Old, P) = Model (F, P)));
         end loop;
      end Prove_Post;
   begin
      F.S := F.S + 1;
      Root := F.S;
      Prove_Post;
   end Init;

end Binary_Trees;
