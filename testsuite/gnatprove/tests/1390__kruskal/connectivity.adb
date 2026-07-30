package body Connectivity
  with SPARK_Mode => On
is

   function Extend (G : Graph; Reached : Vertex_Set)
     return Vertex_Set
   is
      Result_G : Vertex_Set := (for Node in Vertex => False);
   begin
      for Node in Vertex loop
         Result_G (Node) :=
           Reached (Node)
           or else (Node <= G.Size
                    and then (for some Neighbour in Vertex =>
                                Neighbour <= G.Size
                                and then Reached (Neighbour)
                                and then Has_Edge (G, Neighbour, Node)));

         pragma Loop_Invariant
           (for all J in 1 .. Node =>
              Result_G (J) =
                (Reached (J)
                 or else (J <= G.Size
                          and then (for some Neighbour in Vertex =>
                                      Neighbour <= G.Size
                                      and then Reached (Neighbour)
                                      and then Has_Edge (G, Neighbour, J)))));
      end loop;
      return Result_G;
   end Extend;

   procedure Lemma_Extend_Increasing (G : Graph; Reached : Vertex_Set) is
   begin
      --  Each component of Extend is "Reached (Node) or else ...", so it
      --  contains Reached.  Automatic.
      null;
   end Lemma_Extend_Increasing;

   procedure Lemma_Extend_Monotone
     (G : Graph; Petit, Grand : Vertex_Set) is
   begin
      --  If a Node is reached by Petit in one step, the same Witness (Neighbour)
      --  works for Grand since Petit (Neighbour) => Grand (Neighbour).
      null;
   end Lemma_Extend_Monotone;

   procedure Lemma_Closure_Increasing
     (G : Graph; Reached : Vertex_Set; Fuel : Natural) is
   begin
      if Fuel = 0 then
         return;
      end if;

      --  Reached subset Extend (Reached) subset Closure (Extend (Reached)).

      Lemma_Extend_Increasing (G, Reached);
      Lemma_Closure_Increasing (G, Extend (G, Reached), Fuel - 1);
   end Lemma_Closure_Increasing;

   procedure Lemma_Closure_Monotone
     (G : Graph; Petit, Grand : Vertex_Set; Fuel : Natural) is
   begin
      if Fuel = 0 then
         return;
      end if;

      --  One step preserves the inclusion, then induction on the remaining Fuel.

      Lemma_Extend_Monotone (G, Petit, Grand);
      Lemma_Closure_Monotone
        (G, Extend (G, Petit), Extend (G, Grand), Fuel - 1);
   end Lemma_Closure_Monotone;

   procedure Lemma_Closure_Composition
     (G : Graph; Reached : Vertex_Set; N, M : Natural) is
   begin
      if N = 0 then
         return;
      end if;

      --  Closure (A, N+M) = Closure (Extend (A), (N-1)+M), and induction.

      Lemma_Closure_Composition (G, Extend (G, Reached), N - 1, M);
   end Lemma_Closure_Composition;

   procedure Lemma_Closure_One (G : Graph; X : Vertex_Set) is
   begin
      --  Extend (X) being opaque (an abstract array E), the unfolding is pure
      --  symbolic computation : Closure (X, 1) = Closure (E, 0) = E.

      pragma Assert (Closure (G, X, 1) = Closure (G, Extend (G, X), 0));
   end Lemma_Closure_One;

   procedure Lemma_Closure_Fuel_Increasing
     (G : Graph; Reached : Vertex_Set; Fuel : Natural) is
   begin
      --  Closure (A, K+1) = Closure (A, K, then 1 step) = Extend (Closure (A, K)),
      --  which contains Closure (A, K).

      Lemma_Closure_Composition (G, Reached, Fuel, 1);
      Lemma_Closure_One (G, Closure (G, Reached, Fuel));
      Lemma_Extend_Increasing (G, Closure (G, Reached, Fuel));
   end Lemma_Closure_Fuel_Increasing;

   procedure Lemma_Extend_Support (G : Graph; Reached : Vertex_Set) is
   begin
      --  Extend sets Node to true either if it already was (support unchanged),
      --  or under the guard Node <= G.Size.  Automatic.
      null;
   end Lemma_Extend_Support;

   procedure Lemma_Closure_Support
     (G : Graph; Reached : Vertex_Set; Fuel : Natural) is
   begin
      if Fuel = 0 then
         return;
      end if;

      Lemma_Extend_Support (G, Reached);
      Lemma_Closure_Support (G, Extend (G, Reached), Fuel - 1);
   end Lemma_Closure_Support;

   procedure Lemma_Cardinal_Monotone
     (Petit, Grand : Vertex_Set; From_Idx : Positive) is
   begin
      if From_Idx > Max_Vertices then
         return;
      end if;
      Lemma_Cardinal_Monotone (Petit, Grand, From_Idx + 1);
   end Lemma_Cardinal_Monotone;

   procedure Lemma_Cardinal_Strict
     (Petit, Grand : Vertex_Set; From_Idx : Positive) is
   begin
      if Petit (From_Idx) /= Grand (From_Idx) then

         --  Here Petit is false and Grand true (because Included) : Grand counts +1 ;
         --  the tails compare by monotonicity.

         Lemma_Cardinal_Monotone (Petit, Grand, From_Idx + 1);
      else

         --  Equal here : the differing Witness is further, strict by induction.

         Lemma_Cardinal_Strict (Petit, Grand, From_Idx + 1);
      end if;
   end Lemma_Cardinal_Strict;

   procedure Lemma_Cardinal_Singleton (U : Vertex) is

      --  Auxiliary proof : beyond U, the singleton counts nothing more.

      procedure Zero_After (From_Idx : Positive)
        with Ghost,
             Pre  => From_Idx <= Max_Vertices + 1 and then From_Idx > U,
             Post => Cardinal (Singleton (U), From_Idx) = 0,
             Subprogram_Variant => (Increases => From_Idx)
      is
      begin
         if From_Idx > Max_Vertices then
            return;
         end if;
         Zero_After (From_Idx + 1);
      end Zero_After;

      --  Then from 1 to U : only U counts.

      procedure One_Up_To (From_Idx : Positive)
        with Ghost,
             Pre  => From_Idx <= U,
             Post => Cardinal (Singleton (U), From_Idx) = 1,
             Subprogram_Variant => (Increases => From_Idx)
      is
      begin
         if From_Idx = U then
            Zero_After (From_Idx + 1);
         else
            One_Up_To (From_Idx + 1);
         end if;
      end One_Up_To;

   begin
      One_Up_To (1);
   end Lemma_Cardinal_Singleton;

   procedure Lemma_Cardinal_Support (G : Graph; S : Vertex_Set) is

      --  Beyond G.Size, the bounded support forbids any Node : Cardinal = 0.

      procedure Zero_Outside_Support (From_Idx : Positive)
        with Ghost,
             Pre  => From_Idx <= Max_Vertices + 1 and then From_Idx > G.Size
                     and then Bounded_Support (G, S),
             Post => Cardinal (S, From_Idx) = 0,
             Subprogram_Variant => (Increases => From_Idx)
      is
      begin
         if From_Idx > Max_Vertices then
            return;
         end if;
         Zero_Outside_Support (From_Idx + 1);
      end Zero_Outside_Support;

      --  From From_Idx to G.Size : at most one per index.

      procedure Bound_Up_To_Support (From_Idx : Positive)
        with Ghost,
             Pre  => From_Idx <= G.Size + 1 and then Bounded_Support (G, S),
             Post => Cardinal (S, From_Idx) <= G.Size - From_Idx + 1,
             Subprogram_Variant => (Increases => From_Idx)
      is
      begin
         if From_Idx = G.Size + 1 then
            Zero_Outside_Support (From_Idx);
         else
            Bound_Up_To_Support (From_Idx + 1);
         end if;
      end Bound_Up_To_Support;

   begin
      if G.Size = 0 then
         Zero_Outside_Support (1);
      else
         Bound_Up_To_Support (1);
      end if;
   end Lemma_Cardinal_Support;

   procedure Lemma_Fixpoint_Stable
     (G : Graph; X : Vertex_Set; M : Natural) is
   begin
      if M = 0 then
         return;
      end if;

      --  Closure (X, M) = Closure (Closure (X, M-1), 1) = Closure (X, 1)
      --                 = Extend (X) = X.

      Lemma_Fixpoint_Stable (G, X, M - 1);
      Lemma_Closure_Composition (G, X, M - 1, 1);
      Lemma_Closure_One (G, X);
   end Lemma_Fixpoint_Stable;

   procedure Lemma_Strict_Growth
     (G : Graph; A : Vertex_Set; K : Natural)
   is
      Before : constant Vertex_Set := Closure (G, A, K);
      After : constant Vertex_Set := Extend (G, Before);
   begin
      --  After = Closure (A, K+1), contains Before (increasing) and differs from it :
      --  there is thus a gained Node, hence the strict growth of the cardinal.

      --  Closure (A, K+1) = Closure (Before, 1) = Extend (Before) = After.

      Lemma_Extend_Increasing (G, Before);
      Lemma_Closure_Composition (G, A, K, 1);
      Lemma_Closure_One (G, Before);
      pragma Assert (Closure (G, A, K + 1) = After);
      pragma Assert
        (for some P in Vertex => Before (P) /= After (P));
      Lemma_Cardinal_Strict (Before, After, 1);

      --  Carry over to the post-condition.  We avoid direct congruence on the
      --  recursive function Cardinal (costly) : Closure (A, K+1) = After gives
      --  the double inclusion, hence the equality of cardinals by monotonicity.

      pragma Assert (Included (Closure (G, A, K + 1), After));
      pragma Assert (Included (After, Closure (G, A, K + 1)));
      Lemma_Cardinal_Monotone (Closure (G, A, K + 1), After, 1);
      Lemma_Cardinal_Monotone (After, Closure (G, A, K + 1), 1);
   end Lemma_Strict_Growth;

   procedure Lemma_Cumul (G : Graph; A : Vertex_Set; K : Natural) is
   begin
      if K = 0 then
         return;
      end if;

      --  If Closure (A, K-1) were already stable, Closure (A, K) would be too
      --  (contradiction with the precondition) : so K-1 is not stable, we apply
      --  the accumulation to it, then the strict growth of the step K-1 -> K.

      if Extend (G, Closure (G, A, K - 1)) = Closure (G, A, K - 1) then
         Lemma_Closure_Composition (G, A, K - 1, 1);
         Lemma_Fixpoint_Stable (G, Closure (G, A, K - 1), 1);
         pragma Assert (Closure (G, A, K) = Closure (G, A, K - 1));
         pragma Assert (False);
      end if;

      Lemma_Cumul (G, A, K - 1);
      Lemma_Strict_Growth (G, A, K - 1);
   end Lemma_Cumul;

   procedure Lemma_Saturation (G : Graph; U : Vertex) is
      Start : constant Vertex_Set := Singleton (U);
      Ferme  : constant Vertex_Set := Closure (G, Start, G.Size);
   begin
      pragma Assert (Bounded_Support (G, Start));
      if Extend (G, Ferme) /= Ferme then

         --  Not stable => we would have gained G.Size Nodes from a Start of
         --  cardinal 1, i.e. 1 + G.Size Nodes, whereas the support bounds
         --  the number to G.Size.  Contradiction.

         Lemma_Cumul (G, Start, G.Size);
         Lemma_Cardinal_Singleton (U);
         Lemma_Closure_Support (G, Start, G.Size);
         Lemma_Cardinal_Support (G, Ferme);
         pragma Assert (Cardinal (Ferme, 1) >= 1 + G.Size);
         pragma Assert (Cardinal (Ferme, 1) <= G.Size);
         pragma Assert (False);
      end if;
   end Lemma_Saturation;

   procedure Lemma_Closure_Saturated (G : Graph; U : Vertex; M : Natural) is
      Start : constant Vertex_Set := Singleton (U);
      Ferme  : constant Vertex_Set := Closure (G, Start, G.Size);
   begin
      --  Closure (Start, Size + M) = Closure (Closure (Start, Size), M)
      --                             = Closure (Ferme, M) = Ferme (fixed point).

      Lemma_Closure_Composition (G, Start, G.Size, M);
      Lemma_Saturation (G, U);
      Lemma_Fixpoint_Stable (G, Ferme, M);
   end Lemma_Closure_Saturated;

   procedure Lemma_Reflexive (G : Graph; U : Vertex) is
   begin
      --  U is in Singleton (U), and the closure only grows.

      Lemma_Closure_Increasing (G, Singleton (U), G.Size);
   end Lemma_Reflexive;

   procedure Lemma_Transitive (G : Graph; U, V, W : Vertex) is
      Depuis_U : constant Vertex_Set := Closure (G, Singleton (U), G.Size);
   begin
      --  V is reached from U, so Singleton (V) subset Depuis_U.  By
      --  monotonicity, Closure (Singleton (V), Size) subset Closure (Depuis_U, Size)
      --  = Closure (Singleton (U), 2*Size) = Depuis_U (saturation).  Now W is
      --  reached from V, so W is in Depuis_U : W reaches from U.

      Lemma_Closure_Monotone (G, Singleton (V), Depuis_U, G.Size);
      Lemma_Closure_Composition (G, Singleton (U), G.Size, G.Size);
      Lemma_Closure_Saturated (G, U, G.Size);
   end Lemma_Transitive;

   procedure Lemma_Sym_Point (G : Graph; U, X : Vertex; K : Natural) is
   begin
      if K = 0 then

         --  Closure (Singleton (U), 0) = Singleton (U) : X in this set
         --  forces X = U, and then U is in Singleton (X) = Singleton (U).

         return;
      end if;

      declare
         S : constant Vertex_Set := Closure (G, Singleton (U), K - 1);
      begin
         --  Closure (Singleton (U), K) = Extend (S), so X appears in it via Extend.

         Lemma_Closure_Composition (G, Singleton (U), K - 1, 1);
         Lemma_Closure_One (G, S);
         pragma Assert (Closure (G, Singleton (U), K) = Extend (G, S));
         pragma Assert (Extend (G, S) (X));

         if S (X) then

            --  X was already reached at K-1 : induction then one more step.

            Lemma_Sym_Point (G, U, X, K - 1);
            Lemma_Closure_Fuel_Increasing (G, Singleton (X), K - 1);
         else

            --  X is a Neighbour of a Node Neighbour reached at K-1.  We locate it.

            declare
               Found    : Boolean := False;
               The_Neighbour : Vertex  := X;
            begin
               for Neighbour in Vertex loop
                  if not Found and then Neighbour <= G.Size and then S (Neighbour)
                     and then Has_Edge (G, Neighbour, X)
                  then
                     Found    := True;
                     The_Neighbour := Neighbour;
                  end if;

                  pragma Loop_Invariant
                    (if Found then
                       The_Neighbour <= G.Size and then S (The_Neighbour)
                       and then Has_Edge (G, The_Neighbour, X));
                  pragma Loop_Invariant
                    (if not Found then
                       (for all W in 1 .. Neighbour =>
                          not (W <= G.Size and then S (W)
                               and then Has_Edge (G, W, X))));
               end loop;

               pragma Assert (Found);

               --  U reached from The_Neighbour at K-1 (induction).

               Lemma_Sym_Point (G, U, The_Neighbour, K - 1);

               --  Undirected edge : The_Neighbour is reached from X in 1 step.

               Graphs.Symmetry (G, The_Neighbour, X);
               Lemma_Closure_One (G, Singleton (X));
               pragma Assert (Extend (G, Singleton (X)) (The_Neighbour));
               pragma Assert (Closure (G, Singleton (X), 1) (The_Neighbour));
               pragma Assert (Included (Singleton (The_Neighbour),
                                       Closure (G, Singleton (X), 1)));

               --  So Closure (The_Neighbour, K-1) subset Closure (X, 1+(K-1)) = (X, K).

               Lemma_Closure_Monotone
                 (G, Singleton (The_Neighbour), Closure (G, Singleton (X), 1),
                  K - 1);
               Lemma_Closure_Composition (G, Singleton (X), 1, K - 1);
            end;
         end if;
      end;
   end Lemma_Sym_Point;

   procedure Lemma_Symmetric (G : Graph; U, V : Vertex) is
   begin
      Lemma_Sym_Point (G, U, V, G.Size);
   end Lemma_Symmetric;

   procedure Lemma_Extend_Subgraph
     (G1, G2 : Graph; S : Vertex_Set) is
   begin
      --  Component by component : a Neighbour via an edge of G1 is one
      --  via the same edge of G2 (edges included, same sizes).
      null;
   end Lemma_Extend_Subgraph;

   procedure Lemma_Closure_Subgraph
     (G1, G2 : Graph; S : Vertex_Set; Fuel : Natural) is
   begin
      if Fuel = 0 then
         return;
      end if;

      --  One step preserves the inclusion (Extend subgraph), then induction.  We
      --  go through set monotonicity to combine the two closures.

      Lemma_Extend_Subgraph (G1, G2, S);
      Lemma_Closure_Subgraph (G1, G2, Extend (G1, S), Fuel - 1);
      Lemma_Closure_Monotone
        (G2, Extend (G1, S), Extend (G2, S), Fuel - 1);
   end Lemma_Closure_Subgraph;

   procedure Lemma_Reachable_Subgraph (G1, G2 : Graph; U, V : Vertex) is
   begin
      --  V reached from U in G1 (fuel G1.Size = G2.Size) is also reached in G2.

      Lemma_Closure_Subgraph (G1, G2, Singleton (U), G1.Size);
   end Lemma_Reachable_Subgraph;

   procedure Lemma_Closure_Via_Edges
     (G1, G2 : Graph; U, Target : Vertex; Fuel : Natural)
   is
   begin
      --  Support : the closure from U (U <= G1.Size) contains only
      --  Nodes <= G1.Size = G2.Size ; so Target too.

      pragma Assert (Bounded_Support (G1, Singleton (U)));
      Lemma_Closure_Support (G1, Singleton (U), Fuel);

      if Fuel = 0 then

         --  Closure (G1, {U}, 0) = Singleton (U) : Target = U.

         Lemma_Reflexive (G2, U);
         return;
      end if;

      declare
         S : constant Vertex_Set :=
           Closure (G1, Singleton (U), Fuel - 1);
      begin
         Lemma_Closure_Composition (G1, Singleton (U), Fuel - 1, 1);
         Lemma_Closure_One (G1, S);
         pragma Assert (Closure (G1, Singleton (U), Fuel) = Extend (G1, S));
         pragma Assert (Extend (G1, S) (Target));

         if S (Target) then
            Lemma_Closure_Via_Edges (G1, G2, U, Target, Fuel - 1);
         else

            --  Target is a Neighbour (edge of G1) of a Node X in S : we locate
            --  X.  IH : Reachable (G2, U, X) ; edge G1 X--Target connected in
            --  G2 ; transitivity.

            declare
               Found : Boolean := False;
               Le_X   : Vertex  := U;
            begin
               for X in Vertex loop
                  if not Found and then X <= G1.Size and then S (X)
                     and then Has_Edge (G1, X, Target)
                  then
                     Found := True;
                     Le_X   := X;
                  end if;

                  pragma Loop_Invariant
                    (if Found then
                       Le_X <= G1.Size and then S (Le_X)
                       and then Has_Edge (G1, Le_X, Target));
                  pragma Loop_Invariant
                    (if not Found then
                       (for all X2 in 1 .. X =>
                          not (X2 <= G1.Size and then S (X2)
                               and then Has_Edge (G1, X2, Target))));
               end loop;

               pragma Assert (Found);
               Lemma_Closure_Via_Edges (G1, G2, U, Le_X, Fuel - 1);
               Lemma_Transitive (G2, U, Le_X, Target);
            end;
         end if;
      end;
   end Lemma_Closure_Via_Edges;

   procedure Lemma_Reachable_Via_Edges (G1, G2 : Graph; U, V : Vertex) is
   begin
      Lemma_Closure_Via_Edges (G1, G2, U, V, G1.Size);
   end Lemma_Reachable_Via_Edges;

   procedure Lemma_Same_Except_Edge
     (G1, G2 : Graph; U, V, A, B : Vertex) is
   begin
      null;  --  Direct instantiation of Same_Except (G1, G2, U, V) at (A, B).
   end Lemma_Same_Except_Edge;

   procedure Lemma_SE_Trans (G1, G2, G3 : Graph; U, V : Vertex) is
   begin
      for A in Vertex loop
         for B in Vertex loop
            if A <= G1.Size and then B <= G1.Size
               and then (A /= U or else B /= V)
               and then (A /= V or else B /= U)
            then
               Lemma_Same_Except_Edge (G1, G2, U, V, A, B);
               Lemma_Same_Except_Edge (G2, G3, U, V, A, B);
            end if;

            pragma Loop_Invariant
              (for all AA in 1 .. A =>
                 (for all BB in Vertex =>
                    (if AA <= G1.Size and then BB <= G1.Size
                        and then (AA /= U or else BB /= V)
                        and then (AA /= V or else BB /= U)
                        and then (AA < A or else BB <= B)
                     then Has_Edge (G1, AA, BB) = Has_Edge (G3, AA, BB)
                          and then (if Has_Edge (G1, AA, BB)
                                    then Edge_Length (G1, AA, BB)
                                         = Edge_Length (G3, AA, BB)))));
         end loop;
      end loop;
   end Lemma_SE_Trans;

   procedure Lemma_SE_Included (G1, G2 : Graph; U, V : Vertex) is
   begin
      Symmetry (G1, U, V);  --  not Has_Edge (G1, V, U) too.
      for A in Vertex loop
         for B in Vertex loop
            if A <= G1.Size and then B <= G1.Size
               and then (A /= U or else B /= V)
               and then (A /= V or else B /= U)
            then
               Lemma_Same_Except_Edge (G1, G2, U, V, A, B);
            end if;

            pragma Loop_Invariant
              (for all AA in 1 .. A =>
                 (for all BB in Vertex =>
                    (if AA <= G1.Size and then BB <= G1.Size
                        and then Has_Edge (G1, AA, BB)
                        and then (AA < A or else BB <= B)
                     then Has_Edge (G2, AA, BB))));
         end loop;
      end loop;
   end Lemma_SE_Included;

   procedure Lemma_Closure_Add
     (G1, G2 : Graph; X, Y, A, Target : Vertex; Fuel : Natural)
   is
   begin
      pragma Assert (Bounded_Support (G2, Singleton (A)));
      Lemma_Closure_Support (G2, Singleton (A), Fuel);
      --  Target <= G2.Size = G1.Size (support of the closure from A).

      if Fuel = 0 then
         Lemma_Reflexive (G1, A);
         return;
      end if;

      declare
         S : constant Vertex_Set :=
           Closure (G2, Singleton (A), Fuel - 1);
      begin
         Lemma_Closure_Composition (G2, Singleton (A), Fuel - 1, 1);
         Lemma_Closure_One (G2, S);
         pragma Assert (Closure (G2, Singleton (A), Fuel) = Extend (G2, S));
         pragma Assert (Extend (G2, S) (Target));

         if S (Target) then
            Lemma_Closure_Add (G1, G2, X, Y, A, Target, Fuel - 1);
         else
            declare
               Found : Boolean := False;
               Z      : Vertex  := A;
            begin
               for W in Vertex loop
                  if not Found and then W <= G2.Size and then S (W)
                     and then Has_Edge (G2, W, Target)
                  then
                     Found := True;
                     Z := W;
                  end if;
                  pragma Loop_Invariant
                    (if Found then
                       Z <= G2.Size and then S (Z)
                       and then Has_Edge (G2, Z, Target));
                  pragma Loop_Invariant
                    (if not Found then
                       (for all W2 in 1 .. W =>
                          not (W2 <= G2.Size and then S (W2)
                               and then Has_Edge (G2, W2, Target))));
               end loop;
               pragma Assert (Found);

               --  IH : Z is reachable from A in G2 in Fuel-1 steps.
               Lemma_Closure_Add (G1, G2, X, Y, A, Z, Fuel - 1);

               if (Z = X and then Target = Y)
                 or else (Z = Y and then Target = X)
               then
                  --  The edge Z--Target IS {X, Y} : reflexivity suffices to link
                  --  the disjunction of the IH to the goal.
                  Lemma_Reflexive (G1, X);
                  Lemma_Reflexive (G1, Y);
               else
                  --  Z--Target is an edge of G1 : {Z,Target} /= {X,Y}, so
                  --  Same_Except gives Has_Edge (G1) = Has_Edge (G2).
                  pragma Assert (Target <= G2.Size and then Z <= G2.Size);
                  pragma Assert
                    ((Z /= X or else Target /= Y)
                     and then (Z /= Y or else Target /= X));
                  pragma Assert (Has_Edge (G2, Z, Target));
                  Lemma_Same_Except_Edge (G2, G1, X, Y, Z, Target);
                  pragma Assert (Has_Edge (G1, Z, Target));
                  Lemma_Edge (G1, Z, Target);

                  --  Extend each case of the IH by the edge Z--Target.
                  if Reachable (G1, A, Z) then
                     Lemma_Transitive (G1, A, Z, Target);
                  end if;
                  if Reachable (G1, Y, Z) then
                     Lemma_Transitive (G1, Y, Z, Target);
                  end if;
                  if Reachable (G1, X, Z) then
                     Lemma_Transitive (G1, X, Z, Target);
                  end if;
               end if;
            end;
         end if;
      end;
   end Lemma_Closure_Add;

   procedure Lemma_Reachable_Add (G1, G2 : Graph; X, Y, A, B : Vertex) is
   begin
      Lemma_Closure_Add (G1, G2, X, Y, A, B, G2.Size);
   end Lemma_Reachable_Add;

   procedure Lemma_Reachable_Subgraph_All (G1, G2 : Graph) is
   begin
      for U in Vertex loop
         for V in Vertex loop
            if In_Graph (G1, U) and then In_Graph (G1, V)
               and then Reachable (G1, U, V)
            then
               Lemma_Reachable_Subgraph (G1, G2, U, V);
            end if;

            pragma Loop_Invariant
              (for all VV in 1 .. V =>
                 (if In_Graph (G1, U) and then In_Graph (G1, VV)
                     and then Reachable (G1, U, VV)
                  then Reachable (G2, U, VV)));
            pragma Loop_Invariant
              (for all UU in 1 .. U - 1 =>
                 (for all VV in Vertex =>
                    (if In_Graph (G1, UU) and then In_Graph (G1, VV)
                        and then Reachable (G1, UU, VV)
                     then Reachable (G2, UU, VV))));
         end loop;

         pragma Loop_Invariant
           (for all UU in 1 .. U =>
              (for all VV in Vertex =>
                 (if In_Graph (G1, UU) and then In_Graph (G1, VV)
                     and then Reachable (G1, UU, VV)
                  then Reachable (G2, UU, VV))));
      end loop;
   end Lemma_Reachable_Subgraph_All;

   procedure Lemma_Edge (G : Graph; U, V : Vertex) is
      Start : constant Vertex_Set := Singleton (U);
   begin
      --  One step from {U} reaches V, via the Witness Neighbour = U (edge U--V).

      pragma Assert (Start (U));
      pragma Assert (Extend (G, Start) (V));

      --  G.Size >= 1 (since U in 1 .. G.Size), so Closure unfolds at least one
      --  step : Closure (Start, G.Size) = Closure (Extend (Start), G.Size - 1),
      --  which contains Extend (Start), so V.

      Lemma_Closure_Increasing (G, Extend (G, Start), G.Size - 1);
   end Lemma_Edge;

   function Rep_Search (G : Graph; V : Vertex; W : Vertex) return Vertex is
   begin
      if W >= V then
         Lemma_Reflexive (G, V);        --  Reachable (G, V, V)
         return V;
      elsif Reachable (G, W, V) then
         return W;
      else
         return Rep_Search (G, V, W + 1);
      end if;
   end Rep_Search;

   function Is_Representative (G : Graph; V : Vertex) return Boolean is
   begin
      return (for all U in Vertex => (if U < V then not Reachable (G, U, V)));
   end Is_Representative;

   procedure Lemma_Rep_Is_Rep (G : Graph; V : Vertex) is
   begin
      --  If Is_Representative (no U<V Reachable), Rep cannot be < V
      --  (Rep reaches V), so Rep = V ; conversely Rep=V => no X<V.
      null;
   end Lemma_Rep_Is_Rep;

   procedure Lemma_Rep_Same_Comp (G : Graph; U, V : Vertex) is
   begin
      Lemma_Symmetric (G, U, V);                 --  Reachable (G, V, U)
      Lemma_Transitive (G, Rep (G, V), V, U);      --  Rep(V) reaches U
      Lemma_Transitive (G, Rep (G, U), U, V);      --  Rep(U) reaches V
      pragma Assert (Reachable (G, Rep (G, V), U));
      pragma Assert (Reachable (G, Rep (G, U), V));
      --  Rep(U) is the min reaching U : Rep(V) reaches U => Rep(V) >= Rep(U).
      pragma Assert (Rep (G, V) >= Rep (G, U));
      pragma Assert (Rep (G, U) >= Rep (G, V));
   end Lemma_Rep_Same_Comp;

   procedure Lemma_Rep_Transfer (H, G : Graph; W : Vertex) is
   begin
      Lemma_Reachable_Subgraph_All (H, G);
   end Lemma_Rep_Transfer;

   procedure Lemma_Comp_Plus_One
     (K, F : Graph; M : Vertex; From_Idx : Positive) is
   begin
      if From_Idx > K.Size then
         return;
      end if;
      Lemma_Comp_Plus_One (K, F, M, From_Idx + 1);
   end Lemma_Comp_Plus_One;

   procedure Lemma_Nb_Comp_Monotone (H, G : Graph; From_Idx : Positive) is
   begin
      if From_Idx > G.Size then
         return;   --  H.Size = G.Size (Edges_Included) : both equal 0.
      end if;

      --  Reachable (H) => Reachable (G) : so every representative of G is one
      --  in H too (contrapositive), hence at least as many representatives.
      Lemma_Reachable_Subgraph_All (H, G);
      pragma Assert
        (if Is_Representative (G, From_Idx) then Is_Representative (H, From_Idx));

      Lemma_Nb_Comp_Monotone (H, G, From_Idx + 1);
   end Lemma_Nb_Comp_Monotone;

   procedure Lemma_Nb_Comp_Reach (A, B : Graph; From_Idx : Positive) is
   begin
      if From_Idx > A.Size then
         return;   --  A.Size = B.Size : both counts equal 0.
      end if;

      --  Rep in B => rep in A : if From_Idx were not rep of A, an X < From_Idx
      --  would reach it in A, so in B (hypothesis) -> not rep of B either.
      pragma Assert
        (if Is_Representative (B, From_Idx) then Is_Representative (A, From_Idx));

      Lemma_Nb_Comp_Reach (A, B, From_Idx + 1);
   end Lemma_Nb_Comp_Reach;

   procedure Lemma_Nb_Comp_Equiv (A, B : Graph) is
   begin
      --  Equivalence => the two reachability implications => double bound.
      Lemma_Nb_Comp_Reach (A, B, 1);   --  Nb_Comp (B) <= Nb_Comp (A)
      Lemma_Nb_Comp_Reach (B, A, 1);   --  Nb_Comp (A) <= Nb_Comp (B)
   end Lemma_Nb_Comp_Equiv;

   procedure Lemma_Nb_Comp_Cong (K, F : Graph; From_Idx : Positive) is
   begin
      if From_Idx > K.Size then
         return;   --  K.Size = F.Size : both counts equal 0.
      end if;

      --  The agreement of representatives at From_Idx (precondition) gives the same
      --  increment ; the rest by induction.
      Lemma_Nb_Comp_Cong (K, F, From_Idx + 1);
   end Lemma_Nb_Comp_Cong;

   ---------------------------------------------------------------------------
   --  Closure avoiding a forbidden set.
   ---------------------------------------------------------------------------

   function Avoiding_Extend
     (G : Graph; Reached, Forbidden : Vertex_Set)
     return Vertex_Set
   is
      Result_G : Vertex_Set := (for Node in Vertex => False);
   begin
      for Node in Vertex loop
         Result_G (Node) :=
           Reached (Node)
           or else (Node <= G.Size
                    and then not Forbidden (Node)
                    and then (for some Neighbour in Vertex =>
                                Neighbour <= G.Size
                                and then Reached (Neighbour)
                                and then Has_Edge (G, Neighbour, Node)));

         pragma Loop_Invariant
           (for all J in 1 .. Node =>
              Result_G (J) =
                (Reached (J)
                 or else (J <= G.Size
                          and then not Forbidden (J)
                          and then (for some Neighbour in Vertex =>
                                      Neighbour <= G.Size
                                      and then Reached (Neighbour)
                                      and then Has_Edge (G, Neighbour, J)))));
      end loop;
      return Result_G;
   end Avoiding_Extend;

   procedure Lemma_AE_Increasing
     (G : Graph; Reached, Forbidden : Vertex_Set) is
   begin
      --  Each component is "Reached (Node) or else ...".  Automatic.
      null;
   end Lemma_AE_Increasing;

   procedure Lemma_AC_Increasing
     (G : Graph; Reached, Forbidden : Vertex_Set; Fuel : Natural) is
   begin
      if Fuel = 0 then
         return;
      end if;

      Lemma_AE_Increasing (G, Reached, Forbidden);
      Lemma_AC_Increasing
        (G, Avoiding_Extend (G, Reached, Forbidden), Forbidden, Fuel - 1);
   end Lemma_AC_Increasing;

   procedure Lemma_AC_Composition
     (G : Graph; Reached, Forbidden : Vertex_Set; N, M : Natural) is
   begin
      if N = 0 then
         return;
      end if;

      Lemma_AC_Composition
        (G, Avoiding_Extend (G, Reached, Forbidden), Forbidden, N - 1, M);
   end Lemma_AC_Composition;

   procedure Lemma_AC_One
     (G : Graph; Reached, Forbidden : Vertex_Set) is
   begin
      pragma Assert
        (Avoiding_Closure (G, Reached, Forbidden, 1)
         = Avoiding_Closure
             (G, Avoiding_Extend (G, Reached, Forbidden), Forbidden, 0));
   end Lemma_AC_One;

   procedure Lemma_AC_Fuel_Increasing
     (G : Graph; Reached, Forbidden : Vertex_Set; Fuel : Natural) is
   begin
      Lemma_AC_Composition (G, Reached, Forbidden, Fuel, 1);
      Lemma_AC_One
        (G, Avoiding_Closure (G, Reached, Forbidden, Fuel), Forbidden);
      Lemma_AE_Increasing
        (G, Avoiding_Closure (G, Reached, Forbidden, Fuel), Forbidden);
   end Lemma_AC_Fuel_Increasing;

   procedure Lemma_AE_Empty
     (G : Graph; Reached, Forbidden : Vertex_Set)
   is
   begin
      --  The clause "not Forbidden (Node)" is always true : the two
      --  post-conditions (componentwise) coincide.

      pragma Assert
        (for all S in Vertex =>
           Avoiding_Extend (G, Reached, Forbidden) (S)
           = Extend (G, Reached) (S));
   end Lemma_AE_Empty;

   procedure Lemma_AC_Congruence
     (G : Graph;
      Atteints1, Atteints2, Interdits1, Interdits2 : Vertex_Set;
      Fuel : Natural; Target : Vertex) is
   begin
      --  Induction on the Fuel.  We avoid ANY direct congruence on
      --  Avoiding_Closure (opaque RECURSIVE, whose expansion diverges) : we
      --  reduce it to congruence on Avoiding_Extend (opaque NON recursive, thus
      --  bounded).  Varying Reached AS WELL lets the induction absorb
      --  the step change (E1 -> E2), without ever rewriting under Closure.
      if Fuel = 0 then
         return;   --  Avoiding_Closure (_, _, 0) = Reached ; Atteints1 = Atteints2.
      end if;

      declare
         E1 : constant Vertex_Set :=
           Avoiding_Extend (G, Atteints1, Interdits1);
         E2 : constant Vertex_Set :=
           Avoiding_Extend (G, Atteints2, Interdits2);
      begin
         --  Same arguments => same avoiding step (BOUNDED congruence, non recursive).
         pragma Assert (E1 = E2);

         --  Left unfolding (defining post of Avoiding_Closure, C > 0).
         pragma Assert
           (Avoiding_Closure (G, Atteints1, Interdits1, Fuel) (Target)
            = Avoiding_Closure (G, E1, Interdits1, Fuel - 1) (Target));

         --  Induction : goes from (E1, I1) to (E2, I2) (equal arguments).
         Lemma_AC_Congruence
           (G, E1, E2, Interdits1, Interdits2, Fuel - 1, Target);

         --  Right unfolding (defining post).
         pragma Assert
           (Avoiding_Closure (G, Atteints2, Interdits2, Fuel) (Target)
            = Avoiding_Closure (G, E2, Interdits2, Fuel - 1) (Target));
      end;
   end Lemma_AC_Congruence;

   procedure Lemma_AC_Empty
     (G : Graph; Reached, Forbidden : Vertex_Set; Fuel : Natural)
   is
   begin
      if Fuel = 0 then
         return;
      end if;

      --  IH (table) : Avoiding_Closure (A,I,C-1) = Closure (A,C-1).
      Lemma_AC_Empty (G, Reached, Forbidden, Fuel - 1);

      --  EXPLICIT unfolding of the last step, on both sides, via the lemmas
      --  (no raw axiom : we avoid the explosion of the two functions).

      declare
         CEm : constant Vertex_Set :=
           Avoiding_Closure (G, Reached, Forbidden, Fuel - 1);
         Cm  : constant Vertex_Set := Closure (G, Reached, Fuel - 1);
      begin
         --  Avoiding_Closure (A,I,C) = Avoiding_Extend (CEm, I).
         Lemma_AC_Composition (G, Reached, Forbidden, Fuel - 1, 1);
         Lemma_AC_One (G, CEm, Forbidden);
         pragma Assert
           (Avoiding_Closure (G, Reached, Forbidden, Fuel)
            = Avoiding_Extend (G, CEm, Forbidden));

         --  Closure (A,C) = Extend (Cm).
         Lemma_Closure_Composition (G, Reached, Fuel - 1, 1);
         Lemma_Closure_One (G, Cm);
         pragma Assert
           (Closure (G, Reached, Fuel) = Extend (G, Cm));

         --  CEm = Cm (IH), so Avoiding_Extend (CEm,I) = Avoiding_Extend (Cm,I)
         --  and, with no forbidden set, = Extend (Cm).
         pragma Assert (CEm = Cm);
         Lemma_AE_Empty (G, Cm, Forbidden);
         pragma Assert
           (Avoiding_Extend (G, CEm, Forbidden) = Extend (G, Cm));
      end;
   end Lemma_AC_Empty;

   procedure Lemma_First_Step
     (G         : Graph;
      Start    : Vertex;
      Target     : Vertex;
      Forbidden : Vertex_Set;
      Fuel : Natural;
      Neighbour    : out Vertex)
   is
   begin
      Neighbour := Target;

      --  Fuel zero : the closure reduces to the singleton Start, so
      --  Target = Start, which contradicts the precondition.  Empty case.

      if Fuel = 0 then
         pragma Assert
           (Avoiding_Closure (G, Singleton (Start), Forbidden, 0)
            = Singleton (Start));
         pragma Assert (Singleton (Start) (Target));
         pragma Assert (False);
         return;
      end if;

      declare
         Ck : constant Vertex_Set :=
           Avoiding_Closure (G, Singleton (Start), Forbidden, Fuel - 1);
      begin
         --  Avoiding_Closure (Singleton (Start), Fuel) = Avoiding_Extend (Ck).

         Lemma_AC_Composition (G, Singleton (Start), Forbidden, Fuel - 1, 1);
         Lemma_AC_One (G, Ck, Forbidden);
         pragma Assert
           (Avoiding_Closure (G, Singleton (Start), Forbidden, Fuel)
            = Avoiding_Extend (G, Ck, Forbidden));
         pragma Assert (Avoiding_Extend (G, Ck, Forbidden) (Target));

         if Ck (Target) then

            --  Target already reached at the previous step : induction at Fuel - 1,
            --  then we raise the Fuel.

            Lemma_First_Step (G, Start, Target, Forbidden, Fuel - 1, Neighbour);
            Lemma_AC_Fuel_Increasing
              (G, Singleton (Neighbour), Mark (Forbidden, Start), Fuel - 1);
            return;
         end if;

         --  Target not forbidden, with a predecessor P in Ck (via the edge
         --  P -> Target of the last step).

         pragma Assert (not Forbidden (Target));
         pragma Assert
           (for some P in Vertex =>
              P <= G.Size and then Ck (P) and then Has_Edge (G, P, Target));

         declare
            P      : Vertex := Start;
            Found : Boolean := False;
         begin
            for Cand in 1 .. G.Size loop
               if Ck (Cand) and then Has_Edge (G, Cand, Target) then
                  P := Cand;
                  Found := True;
                  exit;
               end if;

               pragma Loop_Invariant (not Found);
               pragma Loop_Invariant
                 (for all Q in 1 .. Cand =>
                    not (Q <= G.Size and then Ck (Q)
                         and then Has_Edge (G, Q, Target)));
            end loop;

            pragma Assert (Found);
            pragma Assert
              (P <= G.Size and then Ck (P) and then Has_Edge (G, P, Target));

            if P = Start then

               --  The predecessor is Start : Target is a direct Neighbour.

               Neighbour := Target;
               Lemma_AC_Increasing
                 (G, Singleton (Target), Mark (Forbidden, Start), Fuel);
               pragma Assert (Singleton (Target) (Target));

            else

               --  Distinct predecessor : induction on Start -> P, then
               --  extension by the edge P -> Target.

               declare
                  Neighbour_P : Vertex;
               begin
                  Lemma_First_Step
                    (G, Start, P, Forbidden, Fuel - 1, Neighbour_P);
                  Neighbour := Neighbour_P;

                  pragma Assert (Target /= Start);
                  pragma Assert (not Mark (Forbidden, Start) (Target));

                  declare
                     Cp : constant Vertex_Set :=
                       Avoiding_Closure
                         (G, Singleton (Neighbour), Mark (Forbidden, Start),
                          Fuel - 1);
                  begin
                     Lemma_AC_Composition
                       (G, Singleton (Neighbour), Mark (Forbidden, Start),
                        Fuel - 1, 1);
                     Lemma_AC_One (G, Cp, Mark (Forbidden, Start));
                     pragma Assert (Cp (P));
                     pragma Assert
                       (Avoiding_Extend
                          (G, Cp, Mark (Forbidden, Start)) (Target));
                     pragma Assert
                       (Avoiding_Closure
                          (G, Singleton (Neighbour), Mark (Forbidden, Start),
                           Fuel) (Target));
                  end;
               end;
            end if;
         end;
      end;
   end Lemma_First_Step;

end Connectivity;
