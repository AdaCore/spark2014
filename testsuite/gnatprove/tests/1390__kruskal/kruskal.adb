with Ada.Assertions;
with Integer_Lists; use Integer_Lists;

package body Kruskal
  with SPARK_Mode => On
is

   procedure lemma_equality_implies_same_list_in_graph (L1,L2: access constant Cell;G:Graph) is
      begin
      if L1=null then return; else lemma_equality_implies_same_list_in_graph(L1.Next,L2.next,G);end if;
   end lemma_equality_implies_same_list_in_graph;

   procedure lemma_keeps_connected_component_add_vertex_list (L : access constant Cell; G:Graph) is
      begin
      return ;
   end lemma_keeps_connected_component_add_vertex_list;


   procedure lemma_last_elem_in_graph (L : access constant Cell; G : Graph) is
   begin
      if L.Next /= null then
         lemma_last_elem_in_graph (L.Next, G);
      end if;
   end lemma_last_elem_in_graph;

   procedure lemma_list_avoid_empty
     (L : access constant Cell; Visited : Visited_Array; G : Graph) is
   begin
      if L /= null then
         lemma_list_avoid_empty (L.Next, Visited, G);
      end if;
   end lemma_list_avoid_empty;

   procedure lemma_path_completeness (Traversal : access constant Cell; G : Graph) is
      Visited : constant Visited_Array := (others => False);
      Start  : constant Vertex := Traversal.Value;
      Ch      : Path :=
        (Path_Found => False, Traversal => Push (null, Start));
   begin
      lemma_last_elem_in_graph (Traversal, G);
      --  With Visited empty, Traversal avoids all the visited ones.
      lemma_list_avoid_empty (Traversal, Visited, G);
      --  Search From_Idx Start = head of Traversal, providing Traversal as
      --  Witness: the completeness clause of Path_Exists guarantees success.
      Path_Exists
        (G, Start, Last_elem (Traversal), Current_Vertex => Start,
         Visited => Visited, Path_Walked => Ch, Witness => Traversal);
      pragma Assert (Ch.Path_Found);
      Free_List (Ch.Traversal);
   end lemma_path_completeness;




      procedure Lemma_One_Visited_Less (i : Positive; Old_Arr, New_Arr : Visited_Array; Target : Vertex) is
begin
   if i <= Old_Arr'Last then
      Lemma_One_Visited_Less (i + 1, Old_Arr, New_Arr, Target);
      end if;
end Lemma_One_Visited_Less;

   procedure lemma_avoid_add
     (L : access constant Cell; Visited, Visited2 : Visited_Array;
      Target : Vertex; G : Graph) is
   begin
      if L /= null then
         lemma_avoid_add (L.Next, Visited, Visited2, Target, G);
      end if;
   end lemma_avoid_add;

   function Findable
     (G : Graph; Start, Target : Vertex; Visited : Visited_Array)
      return Boolean
   is
   begin
      if Start = Target then
         return True;
      elsif Visited (Start) then
         return False;
      end if;

      declare
         New_V  : constant Visited_Array := Update_Visited (Visited, Start);
         Found : Boolean := False;
      begin
         --  Start is newly marked: the not_visited variant decreases, which
         --  legitimizes the recursive calls (in the body and the invariant).

         Lemma_One_Visited_Less (1, Visited, New_V, Start);

         for W in Vertex loop
            if W <= G.Size and then Has_Edge (G, W, Start)
               and then Findable (G, W, Target, New_V)
            then
               Found := True;
            end if;

            pragma Loop_Invariant
              (Found =
                 (for some W2 in 1 .. W =>
                    W2 <= G.Size and then Has_Edge (G, W2, Start)
                    and then Findable (G, W2, Target, New_V)));
         end loop;

         return Found;
      end;
   end Findable;

   procedure Path_Exists
     (G               : Graph;
      Begin_V : Vertex;
      Target          : Vertex;
      Current_Vertex  : Vertex;
      Visited         : Visited_Array;
      Path_Walked : in out Path;
      Witness          : access constant Cell)
   is
      Current     : constant Vertex := Path_Walked.Traversal.Value;

      --  New_Visited IS exactly the update of the Findable model
      --  (Update_Visited (Visited, Current_Vertex)): no rewriting needed
      --  between the code and the model.
      New_Visited : constant Visited_Array := Update_Visited (Visited, Current_Vertex);
   begin
      if Current = Target then
         pragma Assert (Current_Vertex = Target);
         Path_Walked.Path_Found := True;
         return;
      end if;

      if Visited (Current) then
         Path_Walked.Path_Found := False;
         return;
      end if;

      pragma Assert (Current = Current_Vertex);
      Lemma_One_Visited_Less (New_Visited'First, Visited, New_Visited, Current);

      for W in Vertex loop
         --  Witness invariant: if Witness is a valid simple Path toward Target
         --  avoiding Visited, then as long as nothing is Found, the loop has not
         --  gone past the next Node of the Witness.
         pragma Loop_Invariant
           (if Witness /= null and then Witness.Next /= null
               and then list_in_graph (Witness, G)
               and then Last_elem (Witness) = Target
               and then path_avoids (Witness, Visited, G)
               and then simple_path (Witness)
               and then not Path_Walked.Path_Found
            then W <= Witness.Next.Value);

         --  Constant facts of the loop, kept available in the body.
         pragma Loop_Invariant (Current = Current_Vertex);
         pragma Loop_Invariant
           (New_Visited = Update_Visited (Visited, Current_Vertex));

         --  Completeness WITHOUT Witness: every Neighbour already explored (W2 < W)
         --  whose search failed does not reach the Target in the Findable model.
         pragma Loop_Invariant
           (if not Path_Walked.Path_Found then
              (for all W2 in 1 .. W - 1 =>
                 (if W2 <= G.Size and then Has_Edge (G, W2, Current_Vertex)
                  then not Findable
                         (G, W2, Target, Update_Visited (Visited, Current_Vertex)))));

         if In_Graph (G, W) and then Has_Edge (G, W, Current) then
            declare
               New_Path : Path :=
                 (Path_Found => False,
                  Traversal       => Push (Path_Walked.Traversal, W));
               --  Is W the next Node of the Witness?  If so, the tail of the
               --  Witness will be passed to the recursive call as sub-Witness.
               On_Witness : constant Boolean :=
                 Witness /= null and then Witness.Next /= null
                 and then Witness.Next.Value = W;
            begin
               lemma_equality_implies_same_list_in_graph
                 (Path_Walked.Traversal, New_Path.Traversal.Next, G);
               lemma_keeps_connected_component_add_vertex_list
                 (New_Path.Traversal, G);

               --  Recursive call.  When W is the next Node of the Witness, we
               --  pass the tail of the Witness (shorter Path): it avoids
               --  New_Visited = Visited + {Current} (it avoids Visited and does
               --  not contain Current since the Witness is simple), so the
               --  recursive completeness guarantees success.
               if On_Witness then
                  if path_avoids (Witness, Visited, G)
                    and then simple_path (Witness)
                  then
                     lemma_avoid_add
                       (Witness.Next, Visited, New_Visited, Current, G);
                  end if;
                  Path_Exists
                    (G, Begin_V, Target, Current_Vertex => W,
                     Visited => New_Visited, Path_Walked => New_Path,
                     Witness => Witness.Next);
               else
                  Path_Exists
                    (G, Begin_V, Target, Current_Vertex => W,
                     Visited => New_Visited, Path_Walked => New_Path,
                     Witness => null);
               end if;

               if New_Path.Path_Found then

                  --  Success via W: W is Findable, so Current_Vertex too
                  --  (Findable equation, Witness W).

                  pragma Assert
                    (Findable (G, W, Target, Update_Visited (Visited, Current_Vertex)));
                  pragma Assert
                    (W <= G.Size and then Has_Edge (G, W, Current_Vertex));
                  pragma Assert
                    (Findable (G, Current_Vertex, Target, Visited));

                  Free_List (Path_Walked.Traversal);
                  Path_Walked := New_Path;
                  return;
               else

                  --  Failure From_Idx W (= Current_Vertex of the recursive call): W
                  --  does not reach the Target in the model, avoiding New_Visited
                  --  (given directly by the recursive post-condition).

                  pragma Assert
                    (not Findable
                       (G, W, Target, Update_Visited (Visited, Current_Vertex)));
                  Free_List (New_Path.Traversal);
               end if;
            end;
         end if;
      end loop;

      --  On exit (failure), the completeness invariant Covers the WHOLE domain
      --  (1 .. Vertex'Last): no Neighbour of Current leads to the Target while
      --  avoiding New_Visited.  Since Current = Current_Vertex and
      --  New_Visited = Update_Visited (Visited, Current_Vertex), the equation of
      --  Findable gives: the Target is not Findable From_Idx Current_Vertex.

      pragma Assert (not Visited (Current_Vertex));
      pragma Assert (Current_Vertex /= Target);
      pragma Assert
        (for all W in Vertex =>
           (if W <= G.Size and then Has_Edge (G, W, Current_Vertex)
            then not Findable
                   (G, W, Target, Update_Visited (Visited, Current_Vertex))));
      pragma Assert (not Findable (G, Current_Vertex, Target, Visited));

      Path_Walked.Path_Found := False;
   end Path_Exists;



   procedure Lemma_Connected_Reflexive (G : Graph; U : Vertex) is
   begin
      --  Findable (U, U, empty) = (U = U) = True, by the Findable equation.
      null;
   end Lemma_Connected_Reflexive;

   procedure Lemma_Connected_Edge (G : Graph; U, V : Vertex) is
   begin
      --  Findable (U, V, empty): Witness W = V.  The edge is undirected
      --  (Has_Edge (V, U)), and Findable (V, V, .) = True (V = V).

      Symmetry (G, U, V);
      pragma Assert
        (V <= G.Size
         and then Has_Edge (G, V, U)
         and then Findable
                    (G, V, V, Update_Visited (No_Vertex_Visited, U)));
   end Lemma_Connected_Edge;

   procedure Lemma_Findable_To_Reachable
     (G : Graph; U, V : Vertex; Visited : Visited_Array)
   is
   begin
      if U = V then
         Lemma_Reflexive (G, U);
         return;
      end if;

      --  U /= V and Findable: the equation forces not Visited(U) and the existence
      --  of a Neighbour W with Findable(W, V, New_V).

      pragma Assert (not Visited (U));

      declare
         New_V     : constant Visited_Array := Update_Visited (Visited, U);
         Found    : Boolean := False;
         The_Neighbour : Vertex  := U;
      begin
         Lemma_One_Visited_Less (1, Visited, New_V, U);

         for W in Vertex loop
            if not Found and then W <= G.Size and then Has_Edge (G, W, U)
               and then Findable (G, W, V, New_V)
            then
               Found := True;
               The_Neighbour := W;
            end if;

            pragma Loop_Invariant
              (if Found then
                 The_Neighbour <= G.Size and then Has_Edge (G, The_Neighbour, U)
                 and then Findable (G, The_Neighbour, V, New_V));
            pragma Loop_Invariant
              (if not Found then
                 (for all W2 in 1 .. W =>
                    not (W2 <= G.Size and then Has_Edge (G, W2, U)
                         and then Findable (G, W2, V, New_V))));
         end loop;

         pragma Assert (Found);

         --  Reachable (The_Neighbour, V) by induction; Reachable (U, The_Neighbour)
         --  by the edge (undirected); transitivity.

         Lemma_Findable_To_Reachable (G, The_Neighbour, V, New_V);
         Lemma_Edge (G, The_Neighbour, U);
         Lemma_Symmetric (G, The_Neighbour, U);
         Lemma_Transitive (G, U, The_Neighbour, V);
      end;
   end Lemma_Findable_To_Reachable;

   procedure Lemma_Connected_To_Reachable (G : Graph; U, V : Vertex) is
   begin
      Lemma_Findable_To_Reachable (G, U, V, No_Vertex_Visited);
   end Lemma_Connected_To_Reachable;

   procedure Lemma_Avoiding_Closure_To_Findable
     (G : Graph; Start, Target : Vertex; Forbidden : Visited_Array)
   is
   begin
      if Start = Target then
         --  Findable (G, D, D, I) = True (Start = Target).
         return;
      end if;

      declare
         Neighbour      : Vertex;
         Interdits_E : constant Vertex_Set := Vertex_Set (Forbidden);
         Interdits2  : constant Visited_Array := Update_Visited (Forbidden, Start);
      begin
         --  First step: a Neighbour of Start, not forbidden, from which Target is
         --  reached while additionally avoiding Start.
         Lemma_First_Step
           (G, Start, Target, Interdits_E, G.Size, Neighbour);

         --  No self-loop: Neighbour /= Start (otherwise Has_Edge (Start, Start)).
         No_Self_Loop (G, Start);
         pragma Assert (Neighbour /= Start);

         --  The forbidden set of the traversal (Update_Visited) coincides, after
         --  conversion, with Mark (Interdits_E, Start).
         pragma Assert
           (for all K in Vertex =>
              Vertex_Set (Interdits2) (K)
              = Mark (Interdits_E, Start) (K));
         pragma Assert
           (Vertex_Set (Interdits2) = Mark (Interdits_E, Start));

         --  Precondition of the induction: rewriting of the forbidden set
         --  (Mark (Interdits_E, Start) -> Vertex_Set (Interdits2)),
         --  delegated to the ISOLATED congruence lemma (trivial congruence in a small
         --  context, cf. Lemma_AC_Congruence).
         Lemma_AC_Congruence
           (G, Singleton (Neighbour), Singleton (Neighbour),
            Mark (Interdits_E, Start), Vertex_Set (Interdits2),
            G.Size, Target);

         --  Variant: Start becomes visited, so not_visited decreases.
         Lemma_One_Visited_Less (1, Forbidden, Interdits2, Start);

         --  Induction From_Idx the Neighbour.
         Lemma_Avoiding_Closure_To_Findable (G, Neighbour, Target, Interdits2);

         --  Reconstruction: edge Neighbour -> Start (symmetry) + findability
         --  From_Idx Neighbour give the findability From_Idx Start (equation of
         --  Findable, Witness Neighbour).
         Symmetry (G, Start, Neighbour);
         pragma Assert (Has_Edge (G, Neighbour, Start));
         pragma Assert (Findable (G, Neighbour, Target, Interdits2));
         pragma Assert
           (not Forbidden (Start)
            and then Neighbour <= G.Size
            and then Has_Edge (G, Neighbour, Start)
            and then Findable
                       (G, Neighbour, Target, Update_Visited (Forbidden, Start)));
      end;
   end Lemma_Avoiding_Closure_To_Findable;

   procedure Lemma_Reachable_To_Connected (G : Graph; U, V : Vertex) is
   begin
      --  Reachable (G,U,V) = Closure (Singleton (U), G.Size) (V).  Without any
      --  forbidden set, the avoiding closure coincides (Lemma_AC_Empty), so V is
      --  reached by the avoiding closure From_Idx U.
      pragma Assert
        (for all K in Vertex =>
           not Vertex_Set (No_Vertex_Visited) (K));
      Lemma_AC_Empty
        (G, Singleton (U), Vertex_Set (No_Vertex_Visited), G.Size);
      pragma Assert
        (Avoiding_Closure
           (G, Singleton (U), Vertex_Set (No_Vertex_Visited), G.Size)
           = Closure (G, Singleton (U), G.Size));
      pragma Assert
        (Avoiding_Closure
           (G, Singleton (U), Vertex_Set (No_Vertex_Visited),
            G.Size) (V));

      Lemma_Avoiding_Closure_To_Findable (G, U, V, No_Vertex_Visited);
      --  Findable (G, U, V, No_Vertex_Visited) = Connected (G, U, V).
   end Lemma_Reachable_To_Connected;


   function Same_Component
     (G : Graph; V : Vertex; U : Vertex;
      Witness : access constant Cell := null) Return Path
   is
      Traversal : List := null;
      Path_Walked : Path;
   begin
      Traversal:= Push (Traversal,V);
      Path_Walked := (Path_Found => False, Traversal => Traversal);

      --  Visited empty: a valid Path avoids it (necessary for the completeness
      --  clause of Path_Exists), which makes the Witness usable.  We pass
      --  the aggregate (others => False) LITERALLY everywhere, so that it is the
      --  same term as in the post-condition (no array rewriting).

      if Witness /= null and then list_in_graph (Witness, G) then
         lemma_list_avoid_empty (Witness, No_Vertex_Visited, G);
      end if;

      Path_Exists
        (G, V, U, Current_Vertex => V, Visited => No_Vertex_Visited,
         Path_Walked => Path_Walked, Witness => Witness);
      return Path_Walked;
   end Same_Component;



   ---------------------------------------------------------------------------


   ---------------------------------------------------------------------------
   --  Enumerated edges: array of records (U, V, W).  Types at the body level
   --  to allow extracting the sort (Sort) and proving it IN ISOLATION.
   ---------------------------------------------------------------------------

   type Edge_Rec is record
      U, V : Vertex;
      W    : Weight;
   end record;
   type Edge_List is array (Positive range <>) of Edge_Rec;

   --  (A, B) appears as an edge pair in Edges (1 .. Count).
   function Edge_In (Edges : Edge_List; Count : Natural; A, B : Vertex)
     return Boolean
   is
     (for some K in 1 .. Count =>
        K in Edges'Range and then Edges (K).U = A and then Edges (K).V = B)
   with Ghost;

   ---------------------------------------------------------------------------
   --  Insertion sort by weight.  Proves, IN ISOLATION (light context),
   --  that it PRESERVES the set of edge pairs (permutation) and the validity
   --  of each edge.  This is what transfers the completeness of the enumeration to
   --  the selection phase.
   ---------------------------------------------------------------------------

   procedure Sort
     (Edges : in out Edge_List; Count : Natural; G : Graph; N : Vertex_Count)
     with Ghost,
       Pre  => Edges'First = 1 and then Count <= Edges'Last
               and then Count <= Max_Vertices * Max_Vertices
               and then N = G.Size
               and then (for all K in 1 .. Count =>
                           Edges (K).U < Edges (K).V and then Edges (K).V <= N
                           and then Has_Edge (G, Edges (K).U, Edges (K).V)
                           and then Edges (K).W
                                    = Edge_Length (G, Edges (K).U, Edges (K).V)),
       Post => (for all K in 1 .. Count =>
                  Edges (K).U < Edges (K).V and then Edges (K).V <= N
                  and then Has_Edge (G, Edges (K).U, Edges (K).V)
                  and then Edges (K).W
                           = Edge_Length (G, Edges (K).U, Edges (K).V))
               and then
                 (for all A in Vertex =>
                    (for all B in Vertex =>
                       Edge_In (Edges, Count, A, B)
                       = Edge_In (Edges'Old, Count, A, B)))
               --  ASCENDING SORT by weight (necessary for minimality: the
               --  greedy property of Kruskal relies on the order of the weights).
               and then
                 (for all K1 in 1 .. Count =>
                    (for all K2 in 1 .. Count =>
                       (if K1 <= K2 then Edges (K1).W <= Edges (K2).W)));

   procedure Sort
     (Edges : in out Edge_List; Count : Natural; G : Graph; N : Vertex_Count)
   is
   begin
      for I in 2 .. Count loop
         pragma Loop_Invariant
           (for all K in 1 .. Count =>
              Edges (K).U < Edges (K).V and then Edges (K).V <= N
              and then Has_Edge (G, Edges (K).U, Edges (K).V)
              and then Edges (K).W
                       = Edge_Length (G, Edges (K).U, Edges (K).V));
         pragma Loop_Invariant
           (for all A in Vertex =>
              (for all B in Vertex =>
                 Edge_In (Edges, Count, A, B)
                 = Edge_In (Edges'Loop_Entry, Count, A, B)));
         --  Prefix already sorted.
         pragma Loop_Invariant
           (for all K1 in 1 .. I - 1 =>
              (for all K2 in 1 .. I - 1 =>
                 (if K1 <= K2 then Edges (K1).W <= Edges (K2).W)));
         declare
            Key : constant Edge_Rec := Edges (I);
            J   : Natural := I - 1;
         begin
            while J >= 1 and then Edges (J).W > Key.W loop
               pragma Loop_Invariant (J <= I - 1);
               pragma Loop_Invariant
                 (for all K in 1 .. Count =>
                    Edges (K).U < Edges (K).V and then Edges (K).V <= N
                    and then Has_Edge (G, Edges (K).U, Edges (K).V)
                    and then Edges (K).W
                             = Edge_Length (G, Edges (K).U, Edges (K).V));
               --  Shift: Edges = LoopEntry, element I removed (held in Key)
               --  and positions J+2..I shifted from LoopEntry(J+1..I-1).
               pragma Loop_Invariant
                 (for all K in 1 .. J + 1 =>
                    Edges (K) = Edges'Loop_Entry (K));
               pragma Loop_Invariant
                 (for all K in J + 2 .. I =>
                    Edges (K) = Edges'Loop_Entry (K - 1));
               pragma Loop_Invariant
                 (for all K in I + 1 .. Count =>
                    Edges (K) = Edges'Loop_Entry (K));
               pragma Loop_Invariant (Key = Edges'Loop_Entry (I));
               --  Intact prefix 1..J sorted.
               pragma Loop_Invariant
                 (for all K1 in 1 .. J =>
                    (for all K2 in 1 .. J =>
                       (if K1 <= K2 then Edges (K1).W <= Edges (K2).W)));
               --  Shifted part J+2..I: each element > Key.W, and sorted.
               pragma Loop_Invariant
                 (for all K in J + 2 .. I => Edges (K).W > Key.W);
               pragma Loop_Invariant
                 (for all K1 in J + 2 .. I =>
                    (for all K2 in J + 2 .. I =>
                       (if K1 <= K2 then Edges (K1).W <= Edges (K2).W)));
               pragma Loop_Variant (Decreases => J);
               Edges (J + 1) := Edges (J);
               J := J - 1;
            end loop;
            --  Exit: Edges (J).W <= Key.W (or J = 0); Key is inserted at J+1.
            Edges (J + 1) := Key;
            --  The prefix 1..I is now sorted: 1..J <= Key <= J+2..I.
            pragma Assert
              (for all K1 in 1 .. I =>
                 (for all K2 in 1 .. I =>
                    (if K1 <= K2 then Edges (K1).W <= Edges (K2).W)));
         end;
      end loop;
   end Sort;

   ---------------------------------------------------------------------------
   --  "Model" (Ghost) version of Kruskal, without union-find.
   --
   --  Same skeleton as kruskal (enumeration, insertion sort), but the
   --  cycle detection is done by connectivity in the partial tree MST by means
   --  of the ghost function Same_Component (graph traversal).  Its termination
   --  being proven, the termination of Kruskal_Model is too -- no
   --  pragma Annotate/Intentional needed, unlike the union-find
   --  version.
   ---------------------------------------------------------------------------

   procedure Lemma_Add_Subgraph
     (Before, After, Grand : Graph; U0, V0 : Vertex) is
   begin
      --  The added edge is present in Grand (both orientations).
      Symmetry (Grand, U0, V0);
      --  Every edge of After is either {U0, V0} (in Grand above), or an
      --  edge of Before (Same_Except), hence of Grand (Subgraph (Before)).
   end Lemma_Add_Subgraph;

   procedure Lemma_Add_Edges_Included
     (Before, After : Graph; U0, V0 : Vertex) is
   begin
      --  Every edge of Before persists in After: either it is {U0, V0} (present
      --  in After, both orientations), or it is preserved (Same_Except).
      Symmetry (After, U0, V0);
   end Lemma_Add_Edges_Included;

   function Without_Edge (G : Graph; U, V : Vertex) return Graph is
      R : Graph := G;
   begin
      Remove_Edge (R, U, V);
      return R;
   end Without_Edge;

   function Is_Bridge (G : Graph; A, B : Vertex) return Boolean is
   begin
      return A = B or else not Reachable (Without_Edge (G, A, B), A, B);
   end Is_Bridge;

   function Is_Forest (G : Graph) return Boolean is
   begin
      return
        (for all A in Vertex =>
           (for all B in Vertex =>
              (if In_Graph (G, A) and then In_Graph (G, B)
                  and then Has_Edge (G, A, B)
               then Is_Bridge (G, A, B))));
   end Is_Forest;

   procedure Lemma_Forest_Empty (G : Graph) is
   begin
      null;  --  No edge: the forest condition is empty (true).
   end Lemma_Forest_Empty;

   procedure Lemma_Without_Edge_Monotone (H, F : Graph; U, V : Vertex) is
   begin
      --  Every edge of Without_Edge (H,U,V) is an edge of H (hence of F) other
      --  than {U,V}, hence an edge of Without_Edge (F,U,V).
      null;
   end Lemma_Without_Edge_Monotone;

   procedure Lemma_Subforest (H, F : Graph) is
   begin
      --  Each edge of H is an edge of F (bridge in F).  Since Without_Edge
      --  preserves inclusion, removing it from H (subgraph) disconnects too.
      for A in Vertex loop
         for B in Vertex loop
            if In_Graph (H, A) and then In_Graph (H, B)
               and then Has_Edge (H, A, B)
            then
               --  Edge of F; bridge in F; monotonicity => bridge in H.
               Lemma_Without_Edge_Monotone (H, F, A, B);
               pragma Assert (Is_Bridge (F, A, B));   --  not Att (Without_Edge F)
               --  If (A,B) remained reachable in Without_Edge (H), they would be
               --  so in Without_Edge (F) (monotonicity): contradiction.
               if Reachable (Without_Edge (H, A, B), A, B) then
                  Lemma_Reachable_Subgraph
                    (Without_Edge (H, A, B), Without_Edge (F, A, B), A, B);
                  pragma Assert (False);
               end if;
               pragma Assert (Is_Bridge (H, A, B));
            end if;

            pragma Loop_Invariant
              (for all BB in 1 .. B =>
                 (if In_Graph (H, A) and then In_Graph (H, BB)
                     and then Has_Edge (H, A, BB)
                  then Is_Bridge (H, A, BB)));
            pragma Loop_Invariant
              (for all AA in 1 .. A - 1 =>
                 (for all BB in Vertex =>
                    (if In_Graph (H, AA) and then In_Graph (H, BB)
                        and then Has_Edge (H, AA, BB)
                     then Is_Bridge (H, AA, BB))));
         end loop;

         pragma Loop_Invariant
           (for all AA in 1 .. A =>
              (for all BB in Vertex =>
                 (if In_Graph (H, AA) and then In_Graph (H, BB)
                     and then Has_Edge (H, AA, BB)
                  then Is_Bridge (H, AA, BB))));
      end loop;

      pragma Assert (Is_Forest (H));
   end Lemma_Subforest;

   procedure Lemma_Removal_Bridge_Component (F : Graph; U, V : Vertex) is
      K   : constant Graph  := Without_Edge (F, U, V);
      Ru  : constant Vertex := Rep (K, U);
      Rv  : constant Vertex := Rep (K, V);
      M   : constant Vertex := (if Ru >= Rv then Ru else Rv);
   begin
      --  1. The edge {U,V} is a bridge: U and V are no longer reachable in K.
      pragma Assert (Is_Bridge (F, U, V));       --  directly from the precondition
      pragma Assert (not Reachable (K, U, V));

      --  2. K is a subgraph of F (we only removed {U,V}).
      pragma Assert (Same_Except (K, F, U, V));
      --  Symmetric, fixed once: required by Lemma_Reachable_Add in
      --  the loop (avoids a flaky reinstantiation of the quantifier).
      pragma Assert (Same_Except (F, K, U, V));
      pragma Assert (Edges_Included (K, F));

      --  3. Ru /= Rv: otherwise U and V would be reachable in K.
      Lemma_Rep_Same_Comp (K, Ru, U);           --  Rep (K, Ru) = Ru
      Lemma_Rep_Same_Comp (K, Rv, V);           --  Rep (K, Rv) = Rv
      pragma Assert (Reachable (K, Ru, U));
      pragma Assert (Reachable (K, Rv, V));
      if Ru = Rv then
         Lemma_Symmetric (K, Ru, U);           --  Reachable (K, U, Ru)
         Lemma_Transitive (K, U, Ru, V);         --  U ~ Ru = Rv ~ V => U ~ V
         pragma Assert (False);
      end if;
      pragma Assert (Ru /= Rv);

      --  4. Fact 3: M is a representative in K, not in F.
      Lemma_Rep_Is_Rep (K, Ru);
      Lemma_Rep_Is_Rep (K, Rv);
      pragma Assert (Is_Representative (K, M));

      --  Reachable (F, Ru, Rv): via U-V in F.
      Lemma_Edge (F, U, V);                     --  Reachable (F, U, V)
      Lemma_Reachable_Subgraph (K, F, Ru, U);
      Lemma_Reachable_Subgraph (K, F, Rv, V);
      Lemma_Symmetric (F, Rv, V);               --  Reachable (F, V, Rv)
      Lemma_Transitive (F, Ru, U, V);             --  Ru ~ V
      Lemma_Transitive (F, Ru, V, Rv);            --  Ru ~ Rv
      pragma Assert (Reachable (F, Ru, Rv));
      --  rmin = min (Ru,Rv) < M reaches M in F => Rep (F,M) < M.
      Lemma_Symmetric (F, Ru, Rv);              --  Reachable (F, Rv, Ru)
      Lemma_Reflexive (F, M);
      pragma Assert (Reachable (F, Ru, M));    --  M = Ru or Rv
      pragma Assert (Reachable (F, Rv, M));
      pragma Assert (Ru < M or else Rv < M);     --  Ru /= Rv, M = max
      Lemma_Rep_Is_Rep (F, M);
      pragma Assert (not Is_Representative (F, M));

      --  5. Fact 2: everywhere else, same representatives.
      for W in 1 .. F.Size loop
         --  Reachable (K) => Reachable (F): required AT EACH iteration for
         --  the direction Est_Rep (F) => Est_Rep (K) (the pre-loop facts are forgotten
         --  in the loop; only this local call restores them).
         Lemma_Reachable_Subgraph_All (K, F);
         if W /= M then
            --  Easy direction Est_Rep (F,W) => Est_Rep (K,W): by the All above.
            --  Hard direction (when W is not a rep of F): below.
            if not Is_Representative (F, W) then
               declare
                  X0 : constant Vertex := Rep (F, W);
               begin
                  --  X0 < W reaches W in F; we decompose via the edge {U,V}.
                  Lemma_Reachable_Add (K, F, U, V, X0, W);
                  --  Each case forces either Reachable (K, X0, W) (=> not rep K),
                  --  or W = M (excluded).  We help with symmetry/rep.
                  if Reachable (K, V, W) then
                     Lemma_Symmetric (K, V, W);
                     Lemma_Rep_Same_Comp (K, W, V);   --  Rep (K,W)=Rv
                  end if;
                  if Reachable (K, U, W) then
                     Lemma_Symmetric (K, U, W);
                     Lemma_Rep_Same_Comp (K, W, U);   --  Rep (K,W)=Ru
                  end if;
                  if Reachable (K, X0, U) then
                     Lemma_Rep_Same_Comp (K, X0, U);  --  Rep (K,X0)=Ru
                  end if;
                  if Reachable (K, X0, V) then
                     Lemma_Rep_Same_Comp (K, X0, V);  --  Rep (K,X0)=Rv
                  end if;
                  pragma Assert (not Is_Representative (K, W));
               end;
            end if;
            --  Easy direction: Est_Rep (F,W) => Est_Rep (K,W) (transfer to the
            --  subgraph K), ISOLATED lemma.
            Lemma_Rep_Transfer (K, F, W);
            --  Both directions: equality of the representatives at W.
            pragma Assert
              (Is_Representative (K, W) = Is_Representative (F, W));
         end if;

         --  Pre-loop facts to maintain (K, F, M, U, V, Ru, Rv unchanged):
         --  otherwise lost from one iteration to the next and by Lemma_Comp_Plus_One.
         --  Ru /= Rv is SCALAR (trivial preservation) and suffices for the body.
         pragma Loop_Invariant (Ru /= Rv);
         pragma Loop_Invariant (Is_Representative (K, M));
         pragma Loop_Invariant (not Is_Representative (F, M));
         pragma Loop_Invariant
           (for all WW in 1 .. W =>
              (if WW /= M then
                 Is_Representative (K, WW) = Is_Representative (F, WW)));
      end loop;

      --  6. Counting: exactly one more component.
      Lemma_Comp_Plus_One (K, F, M, 1);
   end Lemma_Removal_Bridge_Component;

   procedure Lemma_Removal_Non_Bridge (F : Graph; U, V : Vertex) is
      K : constant Graph := Without_Edge (F, U, V);
   begin
      pragma Assert (Same_Except (K, F, U, V));
      pragma Assert (Edges_Included (K, F));

      if not Has_Edge (F, U, V) then
         --  Without_Edge is a no-op: K and F have the SAME edges, so each
         --  is a subgraph of the other => same components (double monotonicity).
         pragma Assert (Edges_Included (F, K));
         Lemma_Nb_Comp_Monotone (K, F, 1);
         Lemma_Nb_Comp_Monotone (F, K, 1);
         return;
      end if;

      --  {U,V} is a redundant edge: non-bridge => U and V remain
      --  reachable after removal (definition of Is_Bridge, with U /= V).
      pragma Assert (U /= V);
      pragma Assert (Reachable (K, U, V));

      --  Same_Except is symmetric (equalities); we fix both directions once
      --  (facts on constants, required by Lemma_Reachable_Add).
      pragma Assert (Same_Except (K, F, U, V));
      pragma Assert (Same_Except (F, K, U, V));

      --  Reachability equivalence F <=> K, then equality of the representatives.
      for W in 1 .. F.Size loop
         Lemma_Reachable_Subgraph_All (K, F);   --  direction K => F everywhere

         --  Hard direction F => K for the pairs (X, W), X < W.
         for X in 1 .. W - 1 loop
            Lemma_Reachable_Subgraph_All (K, F);
            if Reachable (F, X, W) then
               --  F = K + {U,V} : any reachability in F recomposes in K
               --  since U ~ V still holds there.
               Lemma_Reachable_Add (K, F, U, V, X, W);
               if Reachable (K, X, U) and then Reachable (K, V, W) then
                  Lemma_Transitive (K, X, U, V);
                  Lemma_Transitive (K, X, V, W);
               end if;
               if Reachable (K, X, V) and then Reachable (K, U, W) then
                  Lemma_Symmetric (K, U, V);
                  Lemma_Transitive (K, X, V, U);
                  Lemma_Transitive (K, X, U, W);
               end if;
               pragma Assert (Reachable (K, X, W));
            else
               --  K => F : if (X, W) were reachable in the subgraph K they would
               --  be reachable in F too -- contradiction with the else guard.
               if Reachable (K, X, W) then
                  Lemma_Reachable_Subgraph (K, F, X, W);
                  pragma Assert (False);
               end if;
               pragma Assert (not Reachable (K, X, W));
            end if;
            --  Equality for the current X : F => K (true case) ; K => F (false case).
            pragma Loop_Invariant
              (for all XX in 1 .. X =>
                 Reachable (F, XX, W) = Reachable (K, XX, W));
         end loop;

         --  Both directions coincide for every X < W (invariant above).
         pragma Assert
           (for all X in Vertex =>
              (if X < W then Reachable (F, X, W) = Reachable (K, X, W)));

         --  Identical representative at W (defining post of Is_Representative).
         Lemma_Rep_Transfer (K, F, W);
         pragma Assert
           (Is_Representative (K, W) = Is_Representative (F, W));

         pragma Loop_Invariant
           (for all WW in 1 .. W =>
              (if WW <= F.Size
               then Is_Representative (K, WW) = Is_Representative (F, WW)));
      end loop;

      Lemma_Nb_Comp_Cong (K, F, 1);
   end Lemma_Removal_Non_Bridge;

   procedure Lemma_Restrict_Without_Edge
     (F : Graph; U, V : Vertex; S : Weight_Threshold)
   is
      G1 : constant Graph := Restrict (Without_Edge (F, U, V), S);
      G2 : constant Graph := Without_Edge (Restrict (F, S), U, V);
   begin
      --  Same Nodes and same edges : Has_Edge (Gi, A, B) is equivalent to
      --  "Has_Edge (F, A, B) and length <= S and {A, B} /= {U, V}".
      Symmetry (F, U, V);
      pragma Assert (G1.Size = G2.Size);
      pragma Assert (Edges_Included (G1, G2));
      pragma Assert (Edges_Included (G2, G1));
      Lemma_Nb_Comp_Monotone (G1, G2, 1);
      Lemma_Nb_Comp_Monotone (G2, G1, 1);
   end Lemma_Restrict_Without_Edge;

   procedure Lemma_Restrict_Included (G : Graph; S : Weight_Threshold) is
   begin
      --  Each edge of the thresholded graph is an edge of G (postcondition of
      --  Restrict) : established cell by cell to help instantiation.
      for A in 1 .. G.Size loop
         for B in 1 .. G.Size loop
            pragma Assert
              (if Has_Edge (Restrict (G, S), A, B)
               then Has_Edge (G, A, B));
            pragma Loop_Invariant
              (for all AA in 1 .. A =>
                 (for all BB in Vertex =>
                    (if BB <= G.Size and then Has_Edge (Restrict (G, S), AA, BB)
                     then Has_Edge (G, AA, BB))));
            pragma Loop_Invariant
              (for all BB in 1 .. B =>
                 (if Has_Edge (Restrict (G, S), A, BB)
                  then Has_Edge (G, A, BB)));
         end loop;
      end loop;
   end Lemma_Restrict_Included;

   procedure Lemma_Without_Edge_Included (G : Graph; U, V : Vertex) is
      K : constant Graph := Without_Edge (G, U, V);
   begin
      --  Same_Except (K, G, U, V) : outside {U,V} the edges coincide ; at
      --  {U,V}, K has no edge -- hence every edge of K is an edge of G.
      pragma Assert (Same_Except (K, G, U, V));
      for A in 1 .. G.Size loop
         pragma Loop_Invariant
           (for all AA in 1 .. A - 1 =>
              (for all B in Vertex =>
                 (if B <= G.Size and then Has_Edge (K, AA, B)
                  then Has_Edge (G, AA, B))));
         for B in 1 .. G.Size loop
            pragma Assert
              (if Has_Edge (K, A, B) then Has_Edge (G, A, B));
            pragma Loop_Invariant
              (for all B2 in 1 .. B =>
                 (if Has_Edge (K, A, B2) then Has_Edge (G, A, B2)));
         end loop;
      end loop;
   end Lemma_Without_Edge_Included;

   procedure Lemma_Restrict_Threshold_Monotone
     (G : Graph; W, S : Weight_Threshold)
   is
      RW : constant Graph := Restrict (G, W);
      RS : constant Graph := Restrict (G, S);
   begin
      for A in 1 .. G.Size loop
         pragma Loop_Invariant
           (for all AA in 1 .. A - 1 =>
              (for all B in Vertex =>
                 (if B <= G.Size and then Has_Edge (RW, AA, B)
                  then Has_Edge (RS, AA, B))));
         for B in 1 .. G.Size loop
            pragma Assert (if Has_Edge (RW, A, B) then Has_Edge (RS, A, B));
            pragma Loop_Invariant
              (for all B2 in 1 .. B =>
                 (if Has_Edge (RW, A, B2) then Has_Edge (RS, A, B2)));
         end loop;
      end loop;
   end Lemma_Restrict_Threshold_Monotone;

   procedure Lemma_Restrict_Subgraph (H, G : Graph; S : Weight_Threshold) is
      RH : constant Graph := Restrict (H, S);
      RG : constant Graph := Restrict (G, S);
   begin
      for A in 1 .. H.Size loop
         pragma Loop_Invariant
           (for all AA in 1 .. A - 1 =>
              (for all B in Vertex =>
                 (if B <= H.Size and then Has_Edge (RH, AA, B)
                  then Has_Edge (RG, AA, B))));
         for B in 1 .. H.Size loop
            pragma Assert (if Has_Edge (RH, A, B) then Has_Edge (RG, A, B));
            pragma Loop_Invariant
              (for all B2 in 1 .. B =>
                 (if Has_Edge (RH, A, B2) then Has_Edge (RG, A, B2)));
         end loop;
      end loop;
   end Lemma_Restrict_Subgraph;

   procedure Lemma_Restrict_Add
     (G_Av, G_Ap : Graph; U0, V0, X, Y : Vertex; S : Weight_Threshold)
   is
      RAv : constant Graph := Restrict (G_Av, S);
      RAp : constant Graph := Restrict (G_Ap, S);
   begin
      --  Edges_Included (RAv, RAp) : outside {U0,V0} the edges of G_Av and G_Ap
      --  coincide (Same_Except) ; at {U0,V0}, G_Av has no edge (hence RAv
      --  neither).  Established cell by cell.
      for A in 1 .. G_Av.Size loop
         pragma Loop_Invariant
           (for all AA in 1 .. A - 1 =>
              (for all B in Vertex =>
                 (if B <= G_Av.Size and then Has_Edge (RAv, AA, B)
                  then Has_Edge (RAp, AA, B))));
         for B in 1 .. G_Av.Size loop
            --  An edge of RAv is an edge of G_Av (def Restrict), hence
            --  distinct from {U0,V0} (absent from G_Av) : Same_Except applies here.
            --  Explicit chain (deterministic) : RAv -> G_Av -> (Same_Except)
            --  G_Ap -> RAp.
            if Has_Edge (RAv, A, B) then
               pragma Assert (Has_Edge (G_Av, A, B));
               pragma Assert (Edge_Length (G_Av, A, B) <= S);
               pragma Assert
                 ((A /= U0 or else B /= V0) and then (A /= V0 or else B /= U0));
               pragma Assert (Has_Edge (G_Ap, A, B));
               pragma Assert (Edge_Length (G_Ap, A, B) = Edge_Length (G_Av, A, B));
               pragma Assert (Has_Edge (RAp, A, B));
            end if;
            pragma Loop_Invariant
              (for all B2 in 1 .. B =>
                 (if Has_Edge (RAv, A, B2) then Has_Edge (RAp, A, B2)));
         end loop;
      end loop;
      pragma Assert (Edges_Included (RAv, RAp));
      Lemma_Reachable_Subgraph (RAv, RAp, X, Y);
   end Lemma_Restrict_Add;

   procedure Lemma_Restrict_Complete (G : Graph; S : Weight_Threshold; X, Y : Vertex)
   is
      R : constant Graph := Restrict (G, S);
   begin
      --  Every edge of G has a weight <= S, hence appears in R : Edges_Included.
      for A in 1 .. G.Size loop
         pragma Loop_Invariant
           (for all AA in 1 .. A - 1 =>
              (for all B in Vertex =>
                 (if B <= G.Size and then Has_Edge (G, AA, B)
                  then Has_Edge (R, AA, B))));
         for B in 1 .. G.Size loop
            pragma Assert
              (if Has_Edge (G, A, B) then Has_Edge (R, A, B));
            pragma Loop_Invariant
              (for all B2 in 1 .. B =>
                 (if Has_Edge (G, A, B2) then Has_Edge (R, A, B2)));
         end loop;
      end loop;
      pragma Assert (Edges_Included (G, R));
      Lemma_Reachable_Subgraph (G, R, X, Y);
   end Lemma_Restrict_Complete;

   procedure Lemma_Without_Edge_Absent (G : Graph; U, V : Vertex) is
      K : constant Graph := Without_Edge (G, U, V);
   begin
      --  {U,V} absent : K has exactly the edges of G (Same_Except + no
      --  edge to remove) => each a subgraph of the other => same count.
      pragma Assert (Same_Except (K, G, U, V));
      pragma Assert (Edges_Included (K, G));
      pragma Assert (Edges_Included (G, K));
      Lemma_Nb_Comp_Monotone (K, G, 1);
      Lemma_Nb_Comp_Monotone (G, K, 1);
   end Lemma_Without_Edge_Absent;

   procedure Lemma_Threshold_Sum_Removal_Forest
     (F : Graph; U, V : Vertex; N : Weight_Threshold)
   is
      K : constant Graph   := Without_Edge (F, U, V);
      L : constant Integer := Integer (Edge_Length (F, U, V));
   begin
      --  Removal of the bridge {U,V} in F : one more component.
      pragma Assert (Is_Forest (F));
      pragma Assert (Is_Bridge (F, U, V));    --  every edge of a forest is a bridge
      Lemma_Removal_Bridge_Component (F, U, V);
      pragma Assert (Nb_Components (K) = Nb_Components (F) + 1);

      if N = 0 then
         return;                             --  Threshold_Sum (_, 0) = 0
      end if;

      --  Induction on the prefix [0, N-1[.
      Lemma_Threshold_Sum_Removal_Forest (F, U, V, N - 1);

      --  Threshold term s = N - 1.
      declare
         S  : constant Weight_Threshold := N - 1;
         RF : constant Graph := Restrict (F, S);
         RK : constant Graph := Restrict (K, S);
      begin
         --  Commutation Threshold / removal.
         Lemma_Restrict_Without_Edge (F, U, V, S);
         pragma Assert
           (Nb_Components (RK) = Nb_Components (Without_Edge (RF, U, V)));

         --  RF is a sub-forest of F (Restrict keeps only edges of
         --  F, cf. its postcondition).
         Lemma_Restrict_Included (F, S);
         Lemma_Subforest (RF, F);
         pragma Assert (Is_Forest (RF));

         if S >= L then
            --  {U,V} present in RF (length L <= S) and a bridge (forest RF).
            pragma Assert (Has_Edge (RF, U, V));
            pragma Assert (Is_Bridge (RF, U, V));
            Lemma_Removal_Bridge_Component (RF, U, V);
            pragma Assert (Nb_Components (RK) = Nb_Components (RF) + 1);
            pragma Assert (Integer'Min (L, N) = L);
            pragma Assert (Integer'Min (L, N - 1) = L);
         else
            --  {U,V} absent from RF (length L > S) : removal is a no-op.
            pragma Assert (not Has_Edge (RF, U, V));
            Lemma_Without_Edge_Absent (RF, U, V);
            pragma Assert (Nb_Components (RK) = Nb_Components (RF));
            pragma Assert (Integer'Min (L, N) = N);
            pragma Assert (Integer'Min (L, N - 1) = N - 1);
         end if;
      end;
   end Lemma_Threshold_Sum_Removal_Forest;

   procedure Lemma_Weight_Col_Empty (F : Graph; A : Vertex; C : Positive) is
   begin
      if C > F.Size then
         return;
      end if;
      pragma Assert (Contrib (F, A, C) = 0);   --  A >= C, or {A,C} absent
      Lemma_Weight_Col_Empty (F, A, C + 1);
   end Lemma_Weight_Col_Empty;

   procedure Lemma_Weight_Row_Empty (F : Graph; L : Positive) is
   begin
      if L > F.Size then
         return;
      end if;
      Lemma_Weight_Col_Empty (F, L, 1);
      Lemma_Weight_Row_Empty (F, L + 1);
   end Lemma_Weight_Row_Empty;

   procedure Lemma_Threshold_Sum_Empty (F : Graph; N : Weight_Threshold) is
   begin
      if N = 0 then
         return;
      end if;
      Lemma_Threshold_Sum_Empty (F, N - 1);
      declare
         RF : constant Graph := Restrict (F, N - 1);
      begin
         --  RF subgraph of F ; F without edge => reciprocal inclusion (empty) ;
         --  same components, hence null term.
         Lemma_Restrict_Included (F, N - 1);

         --  F has no edge even outside the case A < B (by symmetry and absence of
         --  self-loop) : Edges_Included (F, RF) is then empty (deterministic).
         for AA in 1 .. F.Size loop
            for BB in 1 .. F.Size loop
               if BB < AA then
                  Symmetry (F, AA, BB);
               elsif BB = AA then
                  No_Self_Loop (F, AA);
               end if;
               pragma Loop_Invariant
                 (for all B2 in 1 .. BB => not Has_Edge (F, AA, B2));
               pragma Loop_Invariant
                 (for all A2 in 1 .. AA - 1 =>
                    (for all B2 in Vertex =>
                       (if B2 <= F.Size then not Has_Edge (F, A2, B2))));
            end loop;
            pragma Loop_Invariant
              (for all A2 in 1 .. AA =>
                 (for all B2 in Vertex =>
                    (if B2 <= F.Size then not Has_Edge (F, A2, B2))));
         end loop;

         pragma Assert (Edges_Included (F, RF));   --  F without edge : vacuous
         Lemma_Nb_Comp_Monotone (RF, F, 1);
         Lemma_Nb_Comp_Monotone (F, RF, 1);
         pragma Assert (Nb_Components (RF) = Nb_Components (F));
      end;
   end Lemma_Threshold_Sum_Empty;

   procedure Lemma_Weight_Is_Threshold_Sum (F : Graph) is
      Found : Boolean := False;
      Ua     : Vertex  := 1;
      Va     : Vertex  := 1;
   begin
      --  Search for an edge {Ua, Va}, Ua < Va (no exit : ghost, no cost).
      for A in 1 .. F.Size loop
         for B in A + 1 .. F.Size loop
            if not Found and then Has_Edge (F, A, B) then
               Ua     := A;
               Va     := B;
               Found := True;
            end if;
            pragma Loop_Invariant
              (if Found then
                 Ua < Va and then Va <= F.Size and then Has_Edge (F, Ua, Va));
            pragma Loop_Invariant
              (if not Found then
                 (for all BB in A + 1 .. B => not Has_Edge (F, A, BB)));
            --  Previous rows (1 .. A-1) carried through the inner loop.
            pragma Loop_Invariant
              (if not Found then
                 (for all AA in 1 .. A - 1 =>
                    (for all BB in Vertex =>
                       (if AA < BB and then BB <= F.Size
                        then not Has_Edge (F, AA, BB)))));
         end loop;
         --  Bridge : the Result_G of the inner loop (Row A) in the
         --  quantified form of the outer invariant.
         pragma Assert
           (if not Found then
              (for all BB in Vertex =>
                 (if A < BB and then BB <= F.Size
                  then not Has_Edge (F, A, BB))));
         pragma Loop_Invariant
           (if Found then
              Ua < Va and then Va <= F.Size and then Has_Edge (F, Ua, Va));
         pragma Loop_Invariant
           (if not Found then
              (for all AA in 1 .. A =>
                 (for all BB in Vertex =>
                    (if AA < BB and then BB <= F.Size
                     then not Has_Edge (F, AA, BB)))));
      end loop;

      if not Found then
         --  No edge : null weight = null threshold sum.
         Lemma_Weight_Row_Empty (F, 1);
         Lemma_Threshold_Sum_Empty (F, Max_Weight);
         return;
      end if;

      --  Bridge edge found : removal then induction on the lightened graph.
      declare
         Fp : constant Graph   := Without_Edge (F, Ua, Va);
         L  : constant Integer := Integer (Edge_Length (F, Ua, Va));
      begin
         Lemma_Without_Edge_Included (F, Ua, Va);
         Lemma_Subforest (Fp, F);
         Lemma_Weight_Removal (F, Ua, Va);
         pragma Assert (Contrib (F, Ua, Va) = To_Big_Integer (L));
         pragma Assert (Total_Weight (Fp) < Total_Weight (F));   --  variant

         Lemma_Threshold_Sum_Removal_Forest (F, Ua, Va, Max_Weight);
         pragma Assert (Integer'Min (L, Max_Weight) = L);

         Lemma_Weight_Is_Threshold_Sum (Fp);   --  induction (strictly smaller weight)
      end;
   end Lemma_Weight_Is_Threshold_Sum;

   procedure Lemma_Threshold_Sum_Removal_Upper_Bound
     (H : Graph; U, V : Vertex; N : Weight_Threshold)
   is
      K : constant Graph   := Without_Edge (H, U, V);
      L : constant Integer := Integer (Edge_Length (H, U, V));
   begin
      --  d = nb_comp (K) - nb_comp (H) : 1 if {U,V} is a bridge, 0 otherwise.
      if Is_Bridge (H, U, V) then
         Lemma_Removal_Bridge_Component (H, U, V);
      else
         Lemma_Removal_Non_Bridge (H, U, V);
      end if;

      if N = 0 then
         return;
      end if;

      Lemma_Threshold_Sum_Removal_Upper_Bound (H, U, V, N - 1);

      declare
         S  : constant Weight_Threshold := N - 1;
         RH : constant Graph := Restrict (H, S);
         RK : constant Graph := Restrict (K, S);
      begin
         Lemma_Restrict_Without_Edge (H, U, V, S);
         pragma Assert
           (Nb_Components (RK) = Nb_Components (Without_Edge (RH, U, V)));
         Lemma_Restrict_Included (H, S);

         if S >= L then
            pragma Assert (Has_Edge (RH, U, V));
            pragma Assert (Integer'Min (L, N) = L);
            pragma Assert (Integer'Min (L, N - 1) = L);
            if Is_Bridge (H, U, V) then
               --  {U,V} remains a bridge in RH : otherwise, by monotonicity of
               --  reachability (RH subgraph of H), U and V would be
               --  reachable in Without_Edge (H) -- contradicts Is_Bridge (H).
               Lemma_Without_Edge_Monotone (RH, H, U, V);
               if Reachable (Without_Edge (RH, U, V), U, V) then
                  Lemma_Reachable_Subgraph
                    (Without_Edge (RH, U, V), Without_Edge (H, U, V), U, V);
                  pragma Assert (False);
               end if;
               pragma Assert (Is_Bridge (RH, U, V));
               Lemma_Removal_Bridge_Component (RH, U, V);
               pragma Assert (Nb_Components (RK) = Nb_Components (RH) + 1);
            else
               --  Redundant edge : removal does not decrease the number of
               --  components of the Threshold (monotonicity).
               Lemma_Without_Edge_Included (RH, U, V);
               Lemma_Nb_Comp_Monotone (Without_Edge (RH, U, V), RH, 1);
               pragma Assert (Nb_Components (RK) >= Nb_Components (RH));
            end if;
         else
            --  {U,V} absent from RH (length L > S) : removal is a no-op.
            pragma Assert (not Has_Edge (RH, U, V));
            Lemma_Without_Edge_Absent (RH, U, V);
            pragma Assert (Nb_Components (RK) = Nb_Components (RH));
            pragma Assert (Integer'Min (L, N) = N);
            pragma Assert (Integer'Min (L, N - 1) = N - 1);
         end if;
      end;
   end Lemma_Threshold_Sum_Removal_Upper_Bound;

   procedure Lemma_Threshold_Sum_Lower_Bound (H : Graph) is
      Found : Boolean := False;
      Ua     : Vertex  := 1;
      Va     : Vertex  := 1;
   begin
      --  Search for an edge {Ua, Va}, Ua < Va (ghost, no cost).
      for A in 1 .. H.Size loop
         for B in A + 1 .. H.Size loop
            if not Found and then Has_Edge (H, A, B) then
               Ua     := A;
               Va     := B;
               Found := True;
            end if;
            pragma Loop_Invariant
              (if Found then
                 Ua < Va and then Va <= H.Size and then Has_Edge (H, Ua, Va));
            pragma Loop_Invariant
              (if not Found then
                 (for all BB in A + 1 .. B => not Has_Edge (H, A, BB)));
            pragma Loop_Invariant
              (if not Found then
                 (for all AA in 1 .. A - 1 =>
                    (for all BB in Vertex =>
                       (if AA < BB and then BB <= H.Size
                        then not Has_Edge (H, AA, BB)))));
         end loop;
         pragma Assert
           (if not Found then
              (for all BB in Vertex =>
                 (if A < BB and then BB <= H.Size
                  then not Has_Edge (H, A, BB))));
         pragma Loop_Invariant
           (if Found then
              Ua < Va and then Va <= H.Size and then Has_Edge (H, Ua, Va));
         pragma Loop_Invariant
           (if not Found then
              (for all AA in 1 .. A =>
                 (for all BB in Vertex =>
                    (if AA < BB and then BB <= H.Size
                     then not Has_Edge (H, AA, BB)))));
      end loop;

      if not Found then
         --  No edge : null threshold sum <= null weight.
         Lemma_Weight_Row_Empty (H, 1);
         Lemma_Threshold_Sum_Empty (H, Max_Weight);
         return;
      end if;

      --  Edge found : removal then induction.
      declare
         Hp : constant Graph   := Without_Edge (H, Ua, Va);
         L  : constant Integer := Integer (Edge_Length (H, Ua, Va));
      begin
         Lemma_Without_Edge_Included (H, Ua, Va);
         Lemma_Weight_Removal (H, Ua, Va);
         pragma Assert (Contrib (H, Ua, Va) = To_Big_Integer (L));
         pragma Assert (Total_Weight (Hp) < Total_Weight (H));   --  variant

         Lemma_Threshold_Sum_Removal_Upper_Bound (H, Ua, Va, Max_Weight);
         pragma Assert (Integer'Min (L, Max_Weight) = L);

         Lemma_Threshold_Sum_Lower_Bound (Hp);
      end;
   end Lemma_Threshold_Sum_Lower_Bound;

   procedure Lemma_Greedy_Nb_Comp (G : Graph; S : Weight_Threshold) is
      T  : constant Graph := Kruskal_Model (G);
      RG : constant Graph := Restrict (G, S);
      RT : constant Graph := Restrict (T, S);
   begin
      --  PHASE 1 : Edges_Connected (RG, RT) -- each edge of RG (weight <= S)
      --  has its endpoints linked in RT (greedy property of T + monotonicity
      --  of the Threshold).
      for A in Vertex loop
         for B in Vertex loop
            if In_Graph (G, A) and then In_Graph (G, B)
               and then Has_Edge (RG, A, B)
            then
               pragma Assert (Has_Edge (G, A, B));
               pragma Assert (Edge_Length (G, A, B) <= S);
               Lemma_Restrict_Threshold_Monotone (T, Edge_Length (G, A, B), S);
               Lemma_Reachable_Subgraph
                 (Restrict (T, Edge_Length (G, A, B)), RT, A, B);
               pragma Assert (Reachable (RT, A, B));
            end if;
            pragma Loop_Invariant
              (for all BB in 1 .. B =>
                 (if In_Graph (G, A) and then In_Graph (G, BB)
                     and then Has_Edge (RG, A, BB)
                  then Reachable (RT, A, BB)));
            pragma Loop_Invariant
              (for all AA in 1 .. A - 1 =>
                 (for all BB in Vertex =>
                    (if In_Graph (G, AA) and then In_Graph (G, BB)
                        and then Has_Edge (RG, AA, BB)
                     then Reachable (RT, AA, BB))));
         end loop;
         pragma Loop_Invariant
           (for all AA in 1 .. A =>
              (for all BB in Vertex =>
                 (if In_Graph (G, AA) and then In_Graph (G, BB)
                     and then Has_Edge (RG, AA, BB)
                  then Reachable (RT, AA, BB))));
      end loop;
      pragma Assert (Edges_Connected (RG, RT));

      --  PHASE 2 : transfer of reachability RG => RT (Closure via edges).
      for U in Vertex loop
         for V in Vertex loop
            if In_Graph (RG, U) and then In_Graph (RG, V)
               and then Reachable (RG, U, V)
            then
               Lemma_Reachable_Via_Edges (RG, RT, U, V);
            end if;
            pragma Loop_Invariant
              (for all VV in 1 .. V =>
                 (if In_Graph (RG, U) and then In_Graph (RG, VV)
                     and then Reachable (RG, U, VV)
                  then Reachable (RT, U, VV)));
            pragma Loop_Invariant
              (for all UU in 1 .. U - 1 =>
                 (for all VV in Vertex =>
                    (if In_Graph (RG, UU) and then In_Graph (RG, VV)
                        and then Reachable (RG, UU, VV)
                     then Reachable (RT, UU, VV))));
         end loop;
         pragma Loop_Invariant
           (for all UU in 1 .. U =>
              (for all VV in Vertex =>
                 (if In_Graph (RG, UU) and then In_Graph (RG, VV)
                     and then Reachable (RG, UU, VV)
                  then Reachable (RT, UU, VV))));
      end loop;

      --  RT more connected than RG => at most as many components.
      Lemma_Nb_Comp_Reach (RG, RT, 1);
   end Lemma_Greedy_Nb_Comp;

   procedure Lemma_Threshold_Sum_Greedy (G, H : Graph; N : Weight_Threshold) is
      T : constant Graph := Kruskal_Model (G);
   begin
      if N = 0 then
         return;
      end if;

      Lemma_Threshold_Sum_Greedy (G, H, N - 1);

      --  Threshold term s = N - 1 : nb_comp (Restrict (T, s))
      --  <= nb_comp (Restrict (G, s)) [greedy] <= nb_comp (Restrict (H, s))
      --  [H subgraph of G].  With nb_comp (T) = nb_comp (H), the term of T
      --  is a lower bound of that of H.
      Lemma_Greedy_Nb_Comp (G, N - 1);
      Lemma_Restrict_Subgraph (H, G, N - 1);
      Lemma_Nb_Comp_Monotone (Restrict (H, N - 1), Restrict (G, N - 1), 1);
      pragma Assert
        (Nb_Components (Restrict (T, N - 1))
         <= Nb_Components (Restrict (H, N - 1)));
   end Lemma_Threshold_Sum_Greedy;

   --  Without_Edge commutes with the addition of ANOTHER edge : removing {A,B} from
   --  G_After (= G_Before + {U0,V0}) gives (G_Before without {A,B}) + {U0,V0}.
   procedure Lemma_Without_Edge_Commute
     (G_Before, G_After : Graph; A, B, U0, V0 : Vertex)
     with Ghost,
       Pre  => G_Before.Size = G_After.Size
               and then In_Graph (G_Before, A) and then In_Graph (G_Before, B)
               and then In_Graph (G_Before, U0) and then In_Graph (G_Before, V0)
               and then Same_Except (G_After, G_Before, U0, V0)
               and then (A /= U0 or else B /= V0)
               and then (A /= V0 or else B /= U0),
       Post => Same_Except
                 (Without_Edge (G_After, A, B), Without_Edge (G_Before, A, B), U0, V0)
               and then Has_Edge (Without_Edge (G_After, A, B), U0, V0)
                        = Has_Edge (G_After, U0, V0);

   procedure Lemma_Without_Edge_Commute
     (G_Before, G_After : Graph; A, B, U0, V0 : Vertex)
   is
      H  : constant Graph := Without_Edge (G_After, A, B);
      G1 : constant Graph := Without_Edge (G_Before, A, B);
   begin
      --  Has_Edge (H, U0, V0) = Has_Edge (G_After, U0, V0) since {U0,V0} /= {A,B}.
      Lemma_Same_Except_Edge (H, G_After, A, B, U0, V0);

      for a in Vertex loop
         for b in Vertex loop
            if a <= G_Before.Size and then b <= G_Before.Size
               and then (a /= U0 or else b /= V0)
               and then (a /= V0 or else b /= U0)
            then
               if (a = A and then b = B) or else (a = B and then b = A) then
                  null;  --  H and G1 do not have {A,B} (Without_Edge) : equal.
               else
                  Lemma_Same_Except_Edge (H, G_After, A, B, a, b);
                  Lemma_Same_Except_Edge (G_After, G_Before, U0, V0, a, b);
                  Lemma_Same_Except_Edge (G1, G_Before, A, B, a, b);
               end if;
            end if;

            pragma Loop_Invariant
              (for all AA in 1 .. a =>
                 (for all BB in Vertex =>
                    (if AA <= G_Before.Size and then BB <= G_Before.Size
                        and then (AA /= U0 or else BB /= V0)
                        and then (AA /= V0 or else BB /= U0)
                        and then (AA < a or else BB <= b)
                     then Has_Edge (H, AA, BB) = Has_Edge (G1, AA, BB)
                          and then (if Has_Edge (H, AA, BB)
                                    then Edge_Length (H, AA, BB)
                                         = Edge_Length (G1, AA, BB)))));
         end loop;
      end loop;
   end Lemma_Without_Edge_Commute;

   --  Case of ONE edge (A,B) : removing it from G_After = G_Before + {U0,V0}
   --  disconnects A and B.  (Local H : no non-scalar in the calling loop.)
   --  Case of an ADDED edge ({A,B} = {U0,V0}) : H has the same edges as
   --  G_Before, where U0 and V0 are not Are_Conn.
   procedure Lemma_Bridge_New
     (G_Before, G_After : Graph; U0, V0, A, B : Vertex)
     with Ghost,
       Pre  => G_Before.Size = G_After.Size
               and then In_Graph (G_Before, U0) and then In_Graph (G_Before, V0)
               and then In_Graph (G_Before, A) and then In_Graph (G_Before, B)
               and then Same_Except (G_After, G_Before, U0, V0)
               and then not Reachable (G_Before, U0, V0)
               and then ((A = U0 and then B = V0)
                         or else (A = V0 and then B = U0)),
       Post => not Reachable (Without_Edge (G_After, A, B), A, B);

   procedure Lemma_Bridge_New
     (G_Before, G_After : Graph; U0, V0, A, B : Vertex)
   is
      H : constant Graph := Without_Edge (G_After, A, B);
   begin
      --  H has the same edges as G_Before (both without {U0,V0}).
      Lemma_SE_Trans (H, G_After, G_Before, U0, V0);
      Lemma_SE_Included (H, G_Before, U0, V0);
      if Reachable (H, A, B) then
         --  Then A~B in G_Before ; but {A,B}={U0,V0} and U0,V0 not Are_Conn.
         Lemma_Reachable_Subgraph (H, G_Before, A, B);
         Lemma_Symmetric (G_Before, A, B);  --  case (V0, U0)
      end if;
   end Lemma_Bridge_New;

   --  Case of an OLD edge ({A,B} /= {U0,V0}) : the decomposition + the guard
   --  forbid any Path A--B avoiding the edge.
   procedure Lemma_Bridge_Old
     (G_Before, G_After : Graph; U0, V0, A, B : Vertex)
     with Ghost,
       Pre  => G_Before.Size = G_After.Size
               and then In_Graph (G_Before, U0) and then In_Graph (G_Before, V0)
               and then In_Graph (G_Before, A) and then In_Graph (G_Before, B)
               and then Same_Except (G_After, G_Before, U0, V0)
               and then Has_Edge (G_After, U0, V0)
               and then not Reachable (G_Before, U0, V0)
               and then Is_Forest (G_Before)
               and then Has_Edge (G_After, A, B)
               and then (A /= U0 or else B /= V0)
               and then (A /= V0 or else B /= U0),
       Post => not Reachable (Without_Edge (G_After, A, B), A, B);

   procedure Lemma_Bridge_Old
     (G_Before, G_After : Graph; U0, V0, A, B : Vertex)
   is
      H  : constant Graph := Without_Edge (G_After, A, B);
      G1 : constant Graph := Without_Edge (G_Before, A, B);
   begin
      Lemma_Same_Except_Edge (G_After, G_Before, U0, V0, A, B);
      pragma Assert (Has_Edge (G_Before, A, B));   --  (A,B) edge of G_Before
      pragma Assert (not Reachable (G1, A, B)); --  Is_Forest (G_Before)
      Lemma_Without_Edge_Commute (G_Before, G_After, A, B, U0, V0);
      Lemma_SE_Included (G1, G_Before, A, B);      --  Edges_Included (G1, G_Before)
      Lemma_Edge (G_Before, A, B);                --  Reachable (G_Before, A, B)

      pragma Assert (Has_Edge (H, U0, V0));  --  = Has_Edge (G_After, U0, V0)
      if Reachable (H, A, B) then
         Lemma_Reachable_Add (G1, H, U0, V0, A, B);
         --  Case 1 : A~B in G1 -> contradicts not Reachable (G1, A, B) (already known).
         --  Case 2 : A~U0 and V0~B in G1 -> U0~A~B~V0 in G_Before.
         if Reachable (G1, A, U0) and then Reachable (G1, V0, B) then
            Lemma_Reachable_Subgraph (G1, G_Before, A, U0);
            Lemma_Reachable_Subgraph (G1, G_Before, V0, B);
            Lemma_Symmetric (G_Before, A, U0);
            Lemma_Symmetric (G_Before, V0, B);
            Lemma_Transitive (G_Before, U0, A, B);
            Lemma_Transitive (G_Before, U0, B, V0);
         end if;
         --  Case 3 : A~V0 and U0~B in G1 -> U0~B~A~V0 in G_Before.
         if Reachable (G1, A, V0) and then Reachable (G1, U0, B) then
            Lemma_Reachable_Subgraph (G1, G_Before, A, V0);
            Lemma_Reachable_Subgraph (G1, G_Before, U0, B);
            Lemma_Symmetric (G_Before, A, V0);
            Lemma_Symmetric (G_Before, U0, B);
            Lemma_Transitive (G_Before, V0, A, B);
            Lemma_Transitive (G_Before, V0, B, U0);
            Lemma_Symmetric (G_Before, V0, U0);  --  -> Reachable (U0, V0)
         end if;

         --  The three cases of the decomposition all lead to a contradiction
         --  (case 1 : not Reachable (G1,A,B) ; cases 2/3 : Reachable (U0,V0)
         --  against the guard).  The branch is therefore impossible.
         pragma Assert (False);
      end if;
   end Lemma_Bridge_Old;

   procedure Lemma_Edge_Bridge
     (G_Before, G_After : Graph; U0, V0, A, B : Vertex)
     with Ghost,
       Pre  => G_Before.Size = G_After.Size
               and then In_Graph (G_Before, U0) and then In_Graph (G_Before, V0)
               and then In_Graph (G_Before, A) and then In_Graph (G_Before, B)
               and then Same_Except (G_After, G_Before, U0, V0)
               and then Has_Edge (G_After, U0, V0)
               and then not Reachable (G_Before, U0, V0)
               and then Is_Forest (G_Before)
               and then Has_Edge (G_After, A, B),
       Post => not Reachable (Without_Edge (G_After, A, B), A, B);

   procedure Lemma_Edge_Bridge
     (G_Before, G_After : Graph; U0, V0, A, B : Vertex)
   is
   begin
      if (A = U0 and then B = V0) or else (A = V0 and then B = U0) then
         Lemma_Bridge_New (G_Before, G_After, U0, V0, A, B);
      else
         Lemma_Bridge_Old (G_Before, G_After, U0, V0, A, B);
      end if;
   end Lemma_Edge_Bridge;

   procedure Lemma_Forest_Add
     (G_Before, G_After : Graph; U0, V0 : Vertex)
   is
   begin
      --  We show Is_Bridge (G_After, A, B) for every edge, via Lemma_Edge_Bridge.
      --  Invariants in the style of the P2 enumeration (completed rows + current
      --  Row), a form that goes through well on the prover side.  Is_Bridge is TRUE on the
      --  diagonal (A = B) by definition, so the self-loop cases are trivial.
      for A in Vertex loop
         for B in Vertex loop
            if In_Graph (G_After, A) and then In_Graph (G_After, B)
               and then Has_Edge (G_After, A, B)
            then
               Lemma_Edge_Bridge (G_Before, G_After, U0, V0, A, B);
               --  We immediately close back the costly term in Is_Bridge (opaque).
               pragma Assert (Is_Bridge (G_After, A, B));
            end if;

            --  Current Row A, columns 1 .. B.
            pragma Loop_Invariant
              (for all BB in 1 .. B =>
                 (if In_Graph (G_After, A) and then In_Graph (G_After, BB)
                     and then Has_Edge (G_After, A, BB)
                  then Is_Bridge (G_After, A, BB)));
            --  Completed rows 1 .. A - 1.
            pragma Loop_Invariant
              (for all AA in 1 .. A - 1 =>
                 (for all BB in Vertex =>
                    (if In_Graph (G_After, AA) and then In_Graph (G_After, BB)
                        and then Has_Edge (G_After, AA, BB)
                     then Is_Bridge (G_After, AA, BB))));
         end loop;

         --  Completed rows 1 .. A.
         pragma Loop_Invariant
           (for all AA in 1 .. A =>
              (for all BB in Vertex =>
                 (if In_Graph (G_After, AA) and then In_Graph (G_After, BB)
                     and then Has_Edge (G_After, AA, BB)
                  then Is_Bridge (G_After, AA, BB))));
      end loop;

      pragma Assert (Is_Forest (G_After));
   end Lemma_Forest_Add;

   function Kruskal_Model (G : Graph) return Graph is
      N   : constant Vertex_Count := G.Size;
      MST : Graph (N) := Empty_Graph (N);

      --  LOOSE bound on the number of edges : Max_Vertices^2 (constant, independent
      --  of N).  Since the array is ghost (Kruskal_Model is Ghost), its size
      --  has no cost at execution.  This loose bound allows a LINEAR
      --  counting invariant (Count <= (U-1)*N + (V-1) < N^2 <= Max_Edges), hence to
      --  prove that the guard never rejects an edge WITHOUT triangular counting.

      Max_Edges : constant Natural := Max_Vertices * Max_Vertices;

      Edges : Edge_List (1 .. Max_Edges) := (others => (U => 1, V => 1, W => 1));
      Count : Natural := 0;

      --  GREEDY (P4) : weight of the LAST edge added to the MST (0 if none).
      --  Since the edges are processed by ascending weight, it is the
      --  MAXIMAL weight of the current MST -> allows thresholding the MST at this level.
      Max_Seen_Weight : Natural := 0;
   begin
      --  1. Enumeration of the edges (canonical orientation U < V).
      for U in 1 .. N loop
         pragma Loop_Invariant (Count <= (U - 1) * N);
         pragma Loop_Invariant
           (for all K in 1 .. Count =>
              Edges (K).U < Edges (K).V and then Edges (K).V <= N
              and then Has_Edge (G, Edges (K).U, Edges (K).V)
              and then Edges (K).W
                       = Edge_Length (G, Edges (K).U, Edges (K).V));
         --  COMPLETENESS : every edge of the already processed rows is recorded.
         pragma Loop_Invariant
           (for all A in Vertex =>
              (for all B in Vertex =>
                 (if A < U and then A < B and then B <= N
                     and then Has_Edge (G, A, B)
                  then (for some K in 1 .. Count =>
                          Edges (K).U = A and then Edges (K).V = B))));

         for V in U + 1 .. N loop
            pragma Loop_Invariant (Count <= (U - 1) * N + (V - 1));
            pragma Loop_Invariant
              (for all K in 1 .. Count =>
                 Edges (K).U < Edges (K).V and then Edges (K).V <= N
                 and then Has_Edge (G, Edges (K).U, Edges (K).V)
                 and then Edges (K).W
                          = Edge_Length (G, Edges (K).U, Edges (K).V));
            pragma Loop_Invariant
              (for all A in Vertex =>
                 (for all B in Vertex =>
                    (if A < B and then B <= N
                        and then (A < U or else (A = U and then B < V))
                        and then Has_Edge (G, A, B)
                     then (for some K in 1 .. Count =>
                             Edges (K).U = A and then Edges (K).V = B))));

            --  The guard never blocks : Count stays under N^2 <= Max_Edges.
            pragma Assert (N <= Max_Vertices);
            pragma Assert (N * N <= Max_Vertices * Max_Vertices);
            pragma Assert (Count < Max_Edges);

            if Has_Edge (G, U, V) and then Count < Max_Edges then
               Count := Count + 1;
               Edges (Count) := (U => U, V => V, W => Edge_Length (G, U, V));
            end if;
         end loop;
      end loop;

      --  2. Insertion sort by ascending weight, EXTRACTED into Sort, which
      --  preserves (proven) the set of edges : the completeness established at
      --  enumeration therefore still holds after the sort.

      pragma Assert
        (for all A in Vertex =>
           (for all B in Vertex =>
              (if A < B and then B <= N and then Has_Edge (G, A, B)
               then Edge_In (Edges, Count, A, B))));

      Sort (Edges, Count, G, N);

      pragma Assert
        (for all A in Vertex =>
           (for all B in Vertex =>
              (if A < B and then B <= N and then Has_Edge (G, A, B)
               then Edge_In (Edges, Count, A, B))));

      --  BASE of acyclicity (P3) : the empty MST (Empty_Graph) is a forest.
      Lemma_Forest_Empty (MST);

      for I in 1 .. Count loop
         pragma Loop_Invariant (Count <= Max_Edges);
         --  ACYCLICITY (P3) : the partial MST is always a forest.
         pragma Loop_Invariant (Is_Forest (MST));
         pragma Loop_Invariant
           (for all K in 1 .. Count =>
              Edges (K).U < Edges (K).V and then Edges (K).V <= N
              and then Has_Edge (G, Edges (K).U, Edges (K).V)
              and then Edges (K).W
                       = Edge_Length (G, Edges (K).U, Edges (K).V));

         --  INCLUSION under construction : at each step, the partial MST
         --  has only edges of G (it only receives enumerated edges).

         pragma Loop_Invariant (Subgraph (MST, G));

         --  Connectivity (for property 2, direction ⇒) : every edge ALREADY processed
         --  has its endpoints connected (Reachable) in the current MST.

         pragma Loop_Invariant
           (for all K in 1 .. I - 1 =>
              Reachable (MST, Edges (K).U, Edges (K).V));

         --  COMPLETENESS : Edges contains all edges of G (established at
         --  enumeration, preserved by Sort ; Edges unchanged in this loop).

         pragma Loop_Invariant
           (for all A in Vertex =>
              (for all B in Vertex =>
                 (if A < B and then B <= N and then Has_Edge (G, A, B)
                  then Edge_In (Edges, Count, A, B))));

         --  GREEDY (P4).  A4 : Edges stays sorted (unchanged in this loop).
         pragma Loop_Invariant
           (for all K1 in 1 .. Count =>
              (for all K2 in 1 .. Count =>
                 (if K1 <= K2 then Edges (K1).W <= Edges (K2).W)));
         --  A1 : the max weight of the MST does not exceed the last edge processed.
         pragma Loop_Invariant
           (Max_Seen_Weight <= (if I = 1 then 0 else Edges (I - 1).W));
         --  A2 : every edge of the MST has a weight <= Max_Seen_Weight.
         pragma Loop_Invariant
           (for all A in Vertex =>
              (for all B in Vertex =>
                 (if A <= N and then B <= N and then Has_Edge (MST, A, B)
                  then Edge_Length (MST, A, B) <= Max_Seen_Weight)));
         --  A3 (GREEDY) : each edge already processed is linked in the MST by
         --  edges of weight <= its own weight (thresholding).
         pragma Loop_Invariant
           (for all K in 1 .. I - 1 =>
              Reachable
                (Restrict (MST, Edges (K).W), Edges (K).U, Edges (K).V));

         declare
            U0 : constant Vertex := Edges (I).U;
            V0 : constant Vertex := Edges (I).V;
            Connection : Path  := Same_Component (MST, U0, V0);
            Are_Conn : constant Boolean := Connection.Path_Found;
         begin
            Free_List (Connection.Traversal);

            --  SCALAR bounds of the current edge Edges (I), fixed once :
            --  avoids re-instantiating the QUANTIFIED invariant on Edges for each
            --  In_Graph below (the scalar facts, for their part, persist without cost,
            --  which eliminates well-formedness failures in this large block).
            pragma Assert (U0 <= N and then V0 <= N and then U0 < V0);

            if Are_Conn then

               --  Edge discarded : U0 and V0 are already Are_Conn (correctness of the
               --  search) -> Reachable in the current MST (unchanged).

               pragma Assert (Connected (MST, U0, V0));
               Lemma_Connected_To_Reachable (MST, U0, V0);

               --  MST unchanged : the already processed edges stay connected.
               pragma Assert
                 (for all K in 1 .. I - 1 =>
                    Reachable (MST, Edges (K).U, Edges (K).V));

               --  GREEDY : MST and Max_Seen_Weight unchanged.  Max_Seen_Weight <= Edges(I).W
               --  (sort) ; A3 for K = I by thresholding above the max.
               pragma Assert (Max_Seen_Weight <= Edges (I).W);
               pragma Assert
                 (for all A in Vertex =>
                    (for all B in Vertex =>
                       (if A <= N and then B <= N and then Has_Edge (MST, A, B)
                        then Edge_Length (MST, A, B) <= Edges (I).W)));
               Lemma_Restrict_Complete (MST, Edges (I).W, U0, V0);
               pragma Assert
                 (for all K in 1 .. I =>
                    Reachable
                      (Restrict (MST, Edges (K).W),
                       Edges (K).U, Edges (K).V));
            else
               declare
                  MST_Before : constant Graph := MST;
               begin
                  --  Well-formedness, established EARLY (clean context) and stable :
                  --  MST_Before is immutable, so these facts hold all the way down.
                  pragma Assert (In_Graph (MST_Before, U0));
                  pragma Assert (In_Graph (MST_Before, V0));

                  --  GREEDY : we CAPTURE, before modification, the facts A2/A3 on
                  --  MST_Before (= current MST), and the bound of the max weight.
                  pragma Assert (Max_Seen_Weight <= Edges (I).W);
                  pragma Assert
                    (for all A in Vertex =>
                       (for all B in Vertex =>
                          (if A <= N and then B <= N
                              and then Has_Edge (MST_Before, A, B)
                           then Edge_Length (MST_Before, A, B) <= Max_Seen_Weight)));
                  pragma Assert
                    (for all K in 1 .. I - 1 =>
                       Reachable
                         (Restrict (MST_Before, Edges (K).W),
                          Edges (K).U, Edges (K).V));

                  pragma Assert (Subgraph (MST_Before, G));

                  --  Capture, BEFORE modification (MST_Before = MST), the
                  --  Connectivity of the already processed edges.
                  pragma Assert
                    (for all K in 1 .. I - 1 =>
                       Reachable (MST_Before, Edges (K).U, Edges (K).V));

                  --  ACYCLICITY (P3) : the search failed, so U0 and V0 are
                  --  NOT Are_Conn (Path_Exists) in MST_Before.  Fact
                  --  captured here (the Reachable reasoning is pushed further
                  --  down, so as not to burden the P1 assertions below).
                  pragma Assert (not Connected (MST_Before, U0, V0));

                  Add_Edge (MST, U0, V0, Edges (I).W);

                  --  Add_Edge only modifies the edge {U0, V0} (Same_Except), which
                  --  is an edge of G (enumeration).  We CAPTURE Same_Except
                  --  here (fresh) : MST is no longer modified afterwards, so this fact
                  --  stays valid until the call to Lemma_Forest_Add below.

                  pragma Assert (Same_Except (MST, MST_Before, U0, V0));

                  --  ACYCLICITY (P3), handled EARLY while Same_Except is fresh :
                  --  by the bridge Reachable => Connected, "not Are_Conn" (captured
                  --  before the addition) gives "not reachable" ; adding the edge
                  --  between two non-reachable Nodes preserves the forest.
                  if Reachable (MST_Before, U0, V0) then
                     Lemma_Reachable_To_Connected (MST_Before, U0, V0);
                     pragma Assert (False);
                  end if;
                  pragma Assert (not Reachable (MST_Before, U0, V0));

                  --  Not reachable => no direct edge (Lemma_Edge).
                  if Has_Edge (MST_Before, U0, V0) then
                     Lemma_Edge (MST_Before, U0, V0);
                     pragma Assert (False);
                  end if;
                  pragma Assert (not Has_Edge (MST_Before, U0, V0));

                  Lemma_Forest_Add (MST_Before, MST, U0, V0);
                  pragma Assert (Is_Forest (MST));

                  Symmetry (G, U0, V0);
                  Symmetry (MST, U0, V0);

                  --  The new edge is indeed an edge of G (enumeration :
                  --  Edges (I) is an edge of G, cf. loop invariant).
                  pragma Assert (Has_Edge (G, U0, V0));

                  --  P1 : the MST remains a subgraph of G.  Frame delegated to an
                  --  ISOLATED lemma (light proof in memory, cf. its declaration) ;
                  --  directly provides the invariant Subgraph (MST, G).
                  pragma Assert (Subgraph (MST_Before, G));
                  Lemma_Add_Subgraph (MST_Before, MST, G, U0, V0);

                  --  Connectivity : the Old_Arr MST is Included in the New_Arr (ISOLATED
                  --  frame), so the old connections are preserved ; the
                  --  new edge Connected U0 and V0.
                  Lemma_Add_Edges_Included (MST_Before, MST, U0, V0);
                  Lemma_Edge (MST, U0, V0);

                  --  The already processed edges stay connected : we lift
                  --  each one, one by one, via subgraph monotonicity (avoids the
                  --  double instantiation of quantifiers, too costly).

                  for KK in 1 .. I - 1 loop
                     --  Scalar bounds of Edges (KK) : well-formedness of the
                     --  In_Graph (MST, Edges (KK)) without re-instantiating the invariant.
                     pragma Assert
                       (Edges (KK).U <= N and then Edges (KK).V <= N);
                     Lemma_Reachable_Subgraph
                       (MST_Before, MST, Edges (KK).U, Edges (KK).V);
                     --  GREEDY : the THRESHOLDED reachability transfers too
                     --  (addition of an edge at an empty location).
                     Lemma_Restrict_Add
                       (MST_Before, MST, U0, V0,
                        Edges (KK).U, Edges (KK).V, Edges (KK).W);
                     pragma Loop_Invariant
                       (for all K in 1 .. KK =>
                          Edges (K).U <= N and then Edges (K).V <= N);
                     pragma Loop_Invariant
                       (for all K in 1 .. KK =>
                          Reachable (MST, Edges (K).U, Edges (K).V));
                     pragma Loop_Invariant
                       (for all K in 1 .. KK =>
                          Reachable
                            (Restrict (MST, Edges (K).W),
                             Edges (K).U, Edges (K).V));
                  end loop;

                  --  Before reassigning Max_Seen_Weight : the old edges have a
                  --  weight <= Old_Arr Max_Seen_Weight <= Edges(I).W (captured with the
                  --  current value of Max_Seen_Weight).
                  pragma Assert
                    (for all A in Vertex =>
                       (for all B in Vertex =>
                          (if A <= N and then B <= N
                              and then Has_Edge (MST_Before, A, B)
                           then Edge_Length (MST_Before, A, B) <= Edges (I).W)));

                  --  GREEDY : the MST gained the edge {U0,V0} of weight Edges(I).W,
                  --  now its maximal weight.
                  Max_Seen_Weight := Edges (I).W;
                  pragma Assert (Edge_Length (MST, U0, V0) = Edges (I).W);
                  --  A2 : old edges <= Old_Arr max <= Edges(I).W ; new
                  --  edge of weight Edges(I).W.
                  pragma Assert
                    (for all A in Vertex =>
                       (for all B in Vertex =>
                          (if A <= N and then B <= N and then Has_Edge (MST, A, B)
                           then Edge_Length (MST, A, B) <= Max_Seen_Weight)));
                  --  A3 for K = I : the new edge links U0,V0 at the Threshold
                  --  Edges(I).W (itself of this weight).
                  pragma Assert (Has_Edge (Restrict (MST, Edges (I).W), U0, V0));
                  Lemma_Edge (Restrict (MST, Edges (I).W), U0, V0);
                  pragma Assert
                    (for all K in 1 .. I =>
                       Reachable
                         (Restrict (MST, Edges (K).W),
                          Edges (K).U, Edges (K).V));
               end;
            end if;

            --  In both cases : U0 and V0 (= Edges (I)) are Are_Conn in the
            --  current MST, and the already processed edges stay so.  The invariant
            --  therefore extends to 1 .. I.

            pragma Assert
              (for all K in 1 .. I - 1 =>
                 Reachable (MST, Edges (K).U, Edges (K).V));
            pragma Assert (Reachable (MST, Edges (I).U, Edges (I).V));
            pragma Assert
              (for all K in 1 .. I =>
                 Reachable (MST, Edges (K).U, Edges (K).V));
         end;
      end loop;

      --  CONCLUSION P2 (⇒) : every enumerated edge is connected in MST
      --  (final invariant) AND every edge of G is enumerated (completeness), so
      --  every edge of G has its endpoints connected : Edges_Connected (G, MST).

      pragma Assert
        (for all K in 1 .. Count =>
           Reachable (MST, Edges (K).U, Edges (K).V));

      --  ACYCLICITY (P3) : MST is no longer modified ; it remains a forest.
      pragma Assert (Is_Forest (MST));

      for A in Vertex loop
         for B in Vertex loop
            if A <= N and then B <= N and then Has_Edge (G, A, B) then
               if A < B then
                  null;  --  Edge_In (A, B) -> a K with Edges (K) = (A, B).
               elsif B < A then
                  Symmetry (G, A, B);            --  Has_Edge (G, B, A)
                  Lemma_Symmetric (MST, B, A);  --  Reachable (MST, A, B)
               end if;
               --  A = B impossible (graph without self-loop).
               pragma Assert (Reachable (MST, A, B));
            end if;

            pragma Loop_Invariant (Is_Forest (MST));
            pragma Loop_Invariant
              (for all BB in 1 .. B =>
                 (if A <= N and then BB <= N and then Has_Edge (G, A, BB)
                  then Reachable (MST, A, BB)));
            pragma Loop_Invariant
              (for all AA in 1 .. A - 1 =>
                 (for all BB in Vertex =>
                    (if AA <= N and then BB <= N and then Has_Edge (G, AA, BB)
                     then Reachable (MST, AA, BB))));
         end loop;

         pragma Loop_Invariant (Is_Forest (MST));
         pragma Loop_Invariant
           (for all AA in 1 .. A =>
              (for all BB in Vertex =>
                 (if AA <= N and then BB <= N and then Has_Edge (G, AA, BB)
                  then Reachable (MST, AA, BB))));
      end loop;

      pragma Assert (Edges_Connected (G, MST));
      pragma Assert (Is_Forest (MST));

      --  GREEDY (P4) : conversion of the final invariant A3 (indexed by Edges) into
      --  a property phrased on G : every edge of G is linked in MST by
      --  edges of weight <= its own weight.
      pragma Assert
        (for all K in 1 .. Count =>
           Reachable
             (Restrict (MST, Edges (K).W), Edges (K).U, Edges (K).V));
      pragma Assert
        (for all K in 1 .. Count =>
           Edges (K).W = Edge_Length (G, Edges (K).U, Edges (K).V));

      for A in Vertex loop
         for B in Vertex loop
            if A <= N and then B <= N and then Has_Edge (G, A, B) then
               if A < B then
                  --  Edge_In (A,B) : a K with Edges (K) = (A,B) and
                  --  Edges (K).W = Edge_Length (G,A,B).
                  pragma Assert
                    (Reachable
                       (Restrict (MST, Edge_Length (G, A, B)), A, B));
               elsif B < A then
                  Symmetry (G, A, B);   --  Has_Edge (G,B,A), equal lengths
                  pragma Assert
                    (Reachable
                       (Restrict (MST, Edge_Length (G, B, A)), B, A));
                  Lemma_Symmetric
                    (Restrict (MST, Edge_Length (G, B, A)), B, A);
                  pragma Assert
                    (Reachable
                       (Restrict (MST, Edge_Length (G, A, B)), A, B));
               end if;
            end if;

            pragma Loop_Invariant
              (for all BB in 1 .. B =>
                 (if A <= N and then BB <= N and then Has_Edge (G, A, BB)
                  then Reachable
                         (Restrict (MST, Edge_Length (G, A, BB)), A, BB)));
            pragma Loop_Invariant
              (for all AA in 1 .. A - 1 =>
                 (for all BB in Vertex =>
                    (if AA <= N and then BB <= N and then Has_Edge (G, AA, BB)
                     then Reachable
                            (Restrict (MST, Edge_Length (G, AA, BB)),
                             AA, BB))));
         end loop;

         pragma Loop_Invariant
           (for all AA in 1 .. A =>
              (for all BB in Vertex =>
                 (if AA <= N and then BB <= N and then Has_Edge (G, AA, BB)
                  then Reachable
                         (Restrict (MST, Edge_Length (G, AA, BB)), AA, BB))));
      end loop;

      return MST;
   end Kruskal_Model;

   procedure Property_Connectivity_Inclusion (G : Graph) is
      Result_G : constant Graph := Kruskal_Model (G);
   begin
      --  Subgraph (property 1) = Edges_Included : the Result_G is a
      --  subgraph of G, so its Connectivity is included in that of G.

      pragma Assert (Result_G.Size = G.Size);
      pragma Assert (Edges_Included (Result_G, G));

      for U in Vertex loop
         for V in Vertex loop
            if In_Graph (G, U) and then In_Graph (G, V)
               and then Reachable (Result_G, U, V)
            then
               Lemma_Reachable_Subgraph (Result_G, G, U, V);
            end if;

            pragma Loop_Invariant
              (for all VV in 1 .. V =>
                 (if In_Graph (G, U) and then In_Graph (G, VV)
                     and then Reachable (Result_G, U, VV)
                  then Reachable (G, U, VV)));
            pragma Loop_Invariant
              (for all UU in 1 .. U - 1 =>
                 (for all VV in Vertex =>
                    (if In_Graph (G, UU) and then In_Graph (G, VV)
                        and then Reachable (Result_G, UU, VV)
                     then Reachable (G, UU, VV))));
         end loop;

         pragma Loop_Invariant
           (for all UU in 1 .. U =>
              (for all VV in Vertex =>
                 (if In_Graph (G, UU) and then In_Graph (G, VV)
                     and then Reachable (Result_G, UU, VV)
                  then Reachable (G, UU, VV))));
      end loop;
   end Property_Connectivity_Inclusion;

   procedure Property_Connectivity (G : Graph) is
      Result_G : constant Graph := Kruskal_Model (G);
   begin
      pragma Assert (Edges_Included (Result_G, G));       --  = Subgraph (P1)
      pragma Assert (Edges_Connected (G, Result_G));     --  P2 direction ⇒

      for U in Vertex loop
         for V in Vertex loop
            if In_Graph (G, U) and then In_Graph (G, V) then
               --  Direction ⇐ (subgraph) and ⇒ (connected edges).
               if Reachable (Result_G, U, V) then
                  Lemma_Reachable_Subgraph (Result_G, G, U, V);
               end if;
               if Reachable (G, U, V) then
                  Lemma_Reachable_Via_Edges (G, Result_G, U, V);
               end if;
            end if;

            pragma Loop_Invariant
              (for all VV in 1 .. V =>
                 (if In_Graph (G, U) and then In_Graph (G, VV)
                  then Reachable (Result_G, U, VV)
                       = Reachable (G, U, VV)));
            pragma Loop_Invariant
              (for all UU in 1 .. U - 1 =>
                 (for all VV in Vertex =>
                    (if In_Graph (G, UU) and then In_Graph (G, VV)
                     then Reachable (Result_G, UU, VV)
                          = Reachable (G, UU, VV))));
         end loop;

         pragma Loop_Invariant
           (for all UU in 1 .. U =>
              (for all VV in Vertex =>
                 (if In_Graph (G, UU) and then In_Graph (G, VV)
                  then Reachable (Result_G, UU, VV)
                       = Reachable (G, UU, VV))));
      end loop;
   end Property_Connectivity;

   procedure Property_Connectivity_Real (G : Graph) is
      Result_G : constant Graph := Kruskal_Model (G);
   begin
      --  Equality of components in the sense of the model (P2 already proven).
      Property_Connectivity (G);
      pragma Assert (Result_G.Size = G.Size);

      for U in Vertex loop
         for V in Vertex loop
            if In_Graph (G, U) and then In_Graph (G, V) then

               --  Connected (Result_G) <=> Reachable (Result_G)
               --                       <=> Reachable (G) <=> Connected (G),
               --  via the two bridges, on each of the two graphs.

               if Connected (Result_G, U, V) then
                  Lemma_Connected_To_Reachable (Result_G, U, V);
               end if;
               if Reachable (Result_G, U, V) then
                  Lemma_Reachable_To_Connected (Result_G, U, V);
               end if;
               if Connected (G, U, V) then
                  Lemma_Connected_To_Reachable (G, U, V);
               end if;
               if Reachable (G, U, V) then
                  Lemma_Reachable_To_Connected (G, U, V);
               end if;
            end if;

            pragma Loop_Invariant
              (for all VV in 1 .. V =>
                 (if In_Graph (G, U) and then In_Graph (G, VV)
                  then Connected (Result_G, U, VV) = Connected (G, U, VV)));
            pragma Loop_Invariant
              (for all UU in 1 .. U - 1 =>
                 (for all VV in Vertex =>
                    (if In_Graph (G, UU) and then In_Graph (G, VV)
                     then Connected (Result_G, UU, VV) = Connected (G, UU, VV))));
         end loop;

         pragma Loop_Invariant
           (for all UU in 1 .. U =>
              (for all VV in Vertex =>
                 (if In_Graph (G, UU) and then In_Graph (G, VV)
                  then Connected (Result_G, UU, VV) = Connected (G, UU, VV))));
      end loop;
   end Property_Connectivity_Real;

   procedure Property_Acyclicity (G : Graph) is
      Result_G : constant Graph := Kruskal_Model (G);
   begin
      --  Kruskal_Model guarantees Is_Forest (Result_G).  For each edge (U, V),
      --  Is_Forest gives Is_Bridge (U, V) ; since an edge verifies U /= V (no
      --  self-loop), Is_Bridge reduces to "not Reachable (Without_Edge ...)".
      pragma Assert (Is_Forest (Result_G));
      pragma Assert (Result_G.Size = G.Size);

      for U in Vertex loop
         for V in Vertex loop
            if In_Graph (G, U) and then In_Graph (G, V)
               and then Has_Edge (Result_G, U, V)
            then
               No_Self_Loop (Result_G, U);   --  Has_Edge (U, V) => U /= V
               pragma Assert (U /= V);
               pragma Assert (Is_Bridge (Result_G, U, V));
               pragma Assert
                 (not Reachable (Without_Edge (Result_G, U, V), U, V));
            end if;

            pragma Loop_Invariant
              (for all VV in 1 .. V =>
                 (if In_Graph (G, U) and then In_Graph (G, VV)
                     and then Has_Edge (Result_G, U, VV)
                  then not Reachable
                         (Without_Edge (Result_G, U, VV), U, VV)));
            pragma Loop_Invariant
              (for all UU in 1 .. U - 1 =>
                 (for all VV in Vertex =>
                    (if In_Graph (G, UU) and then In_Graph (G, VV)
                        and then Has_Edge (Result_G, UU, VV)
                     then not Reachable
                            (Without_Edge (Result_G, UU, VV), UU, VV))));
         end loop;

         pragma Loop_Invariant
           (for all UU in 1 .. U =>
              (for all VV in Vertex =>
                 (if In_Graph (G, UU) and then In_Graph (G, VV)
                     and then Has_Edge (Result_G, UU, VV)
                  then not Reachable
                         (Without_Edge (Result_G, UU, VV), UU, VV))));
      end loop;
   end Property_Acyclicity;

   procedure Property_Acyclicity_Real (G : Graph) is
      Result_G : constant Graph := Kruskal_Model (G);
   begin
      Property_Acyclicity (G);
      pragma Assert (Result_G.Size = G.Size);

      --  For each edge (U, V) of Result_G : the Reachable version gives
      --  not Reachable (Without_Edge (Result_G, U, V), U, V) ; by contrapositive of the
      --  bridge Connected => Reachable, we obtain not Connected.

      for U in Vertex loop
         for V in Vertex loop
            if In_Graph (G, U) and then In_Graph (G, V)
               and then Has_Edge (Result_G, U, V)
            then
               --  Without_Edge is a function (deterministic) : all its calls
               --  below denote the same graph.
               pragma Assert
                 (not Reachable (Without_Edge (Result_G, U, V), U, V));
               if Connected (Without_Edge (Result_G, U, V), U, V) then
                  Lemma_Connected_To_Reachable
                    (Without_Edge (Result_G, U, V), U, V);
                  pragma Assert (False);
               end if;
               pragma Assert
                 (not Connected (Without_Edge (Result_G, U, V), U, V));
            end if;

            pragma Loop_Invariant
              (for all VV in 1 .. V =>
                 (if In_Graph (G, U) and then In_Graph (G, VV)
                     and then Has_Edge (Result_G, U, VV)
                  then not Connected (Without_Edge (Result_G, U, VV), U, VV)));
            pragma Loop_Invariant
              (for all UU in 1 .. U - 1 =>
                 (for all VV in Vertex =>
                    (if In_Graph (G, UU) and then In_Graph (G, VV)
                        and then Has_Edge (Result_G, UU, VV)
                     then not Connected
                            (Without_Edge (Result_G, UU, VV), UU, VV))));
         end loop;

         pragma Loop_Invariant
           (for all UU in 1 .. U =>
              (for all VV in Vertex =>
                 (if In_Graph (G, UU) and then In_Graph (G, VV)
                     and then Has_Edge (Result_G, UU, VV)
                  then not Connected
                         (Without_Edge (Result_G, UU, VV), UU, VV))));
      end loop;
   end Property_Acyclicity_Real;

   procedure Lemma_Columns_Cong (K, G : Graph; A : Vertex; C : Positive) is
   begin
      if C > G.Size then
         return;
      end if;
      Lemma_Columns_Cong (K, G, A, C + 1);
   end Lemma_Columns_Cong;

   procedure Lemma_Columns_Diff (K, G : Graph; U, V : Vertex; C : Positive) is
   begin
      if C > G.Size then
         return;
      end if;
      Lemma_Columns_Diff (K, G, U, V, C + 1);
   end Lemma_Columns_Diff;

   procedure Lemma_Rows_Diff (K, G : Graph; U, V : Vertex; L : Positive) is
   begin
      if L > G.Size then
         return;
      end if;
      if L = U then
         Lemma_Columns_Diff (K, G, U, V, 1);
      else
         Lemma_Columns_Cong (K, G, L, 1);
      end if;
      Lemma_Rows_Diff (K, G, U, V, L + 1);
   end Lemma_Rows_Diff;

   procedure Lemma_Weight_Removal (G : Graph; U, V : Vertex) is
      K : constant Graph := Without_Edge (G, U, V);
   begin
      --  K = G deprived of {U, V} : Same_Except (K, G, U, V), same size, and K no
      --  longer has the edge {U, V}.  We deduce the hypotheses (contributions) of
      --  Lemma_Rows_Diff, then apply it.

      pragma Assert (K.Size = G.Size);
      pragma Assert (not Has_Edge (K, U, V));
      pragma Assert (Contrib (K, U, V) = 0);

      --  Rows A /= U : every canonical cell (A, B) is outside the pair
      --  {U, V}, hence unchanged (Same_Except) ; equal contributions.
      pragma Assert
        (for all A in 1 .. Max_Vertices =>
           (if A /= U then
              (for all B in 1 .. Max_Vertices + 1 =>
                 Contrib (K, A, B) = Contrib (G, A, B))));

      --  Row U : cells (U, B) with B /= V outside the pair ; equal.
      pragma Assert
        (for all B in 1 .. Max_Vertices + 1 =>
           (if B /= V then Contrib (K, U, B) = Contrib (G, U, B)));

      Lemma_Rows_Diff (K, G, U, V, 1);
   end Lemma_Weight_Removal;

   procedure Lemma_Kruskal_Same_Comp (G : Graph) is
      T : constant Graph := Kruskal_Model (G);
   begin
      --  T => G : T is a subgraph of G (P1).
      Lemma_Reachable_Subgraph_All (T, G);

      --  G => T : every edge of G is linked in T (Edges_Connected, P2),
      --  hence the transfer of reachability by Closure.
      for U in Vertex loop
         for V in Vertex loop
            if In_Graph (G, U) and then In_Graph (G, V)
               and then Reachable (G, U, V)
            then
               Lemma_Reachable_Via_Edges (G, T, U, V);
            end if;
            pragma Loop_Invariant
              (for all VV in 1 .. V =>
                 (if In_Graph (G, U) and then In_Graph (G, VV)
                     and then Reachable (G, U, VV)
                  then Reachable (T, U, VV)));
            pragma Loop_Invariant
              (for all UU in 1 .. U - 1 =>
                 (for all VV in Vertex =>
                    (if In_Graph (G, UU) and then In_Graph (G, VV)
                        and then Reachable (G, UU, VV)
                     then Reachable (T, UU, VV))));
         end loop;
         pragma Loop_Invariant
           (for all UU in 1 .. U =>
              (for all VV in Vertex =>
                 (if In_Graph (G, UU) and then In_Graph (G, VV)
                     and then Reachable (G, UU, VV)
                  then Reachable (T, UU, VV))));
      end loop;

      pragma Assert
        (for all U in Vertex =>
           (for all V in Vertex =>
              (if In_Graph (T, U) and then In_Graph (T, V)
               then Reachable (T, U, V) = Reachable (G, U, V))));
      Lemma_Nb_Comp_Equiv (T, G);
   end Lemma_Kruskal_Same_Comp;

   procedure Lemma_Covers_Same_Comp (H, G : Graph) is
   begin
      --  H => G : H is a subgraph of G.
      Lemma_Reachable_Subgraph_All (H, G);

      --  G => H : by the bridge Reachable <-> Connected and Covers (same Connected).
      for U in Vertex loop
         for V in Vertex loop
            if In_Graph (G, U) and then In_Graph (G, V)
               and then Reachable (G, U, V)
            then
               Lemma_Reachable_To_Connected (G, U, V);   --  Connected (G,U,V)
               pragma Assert (Connected (H, U, V));           --  Covers
               Lemma_Connected_To_Reachable (H, U, V);    --  Reachable (H,U,V)
            end if;
            pragma Loop_Invariant
              (for all VV in 1 .. V =>
                 (if In_Graph (G, U) and then In_Graph (G, VV)
                     and then Reachable (G, U, VV)
                  then Reachable (H, U, VV)));
            pragma Loop_Invariant
              (for all UU in 1 .. U - 1 =>
                 (for all VV in Vertex =>
                    (if In_Graph (G, UU) and then In_Graph (G, VV)
                        and then Reachable (G, UU, VV)
                     then Reachable (H, UU, VV))));
         end loop;
         pragma Loop_Invariant
           (for all UU in 1 .. U =>
              (for all VV in Vertex =>
                 (if In_Graph (G, UU) and then In_Graph (G, VV)
                     and then Reachable (G, UU, VV)
                  then Reachable (H, UU, VV))));
      end loop;

      pragma Assert
        (for all U in Vertex =>
           (for all V in Vertex =>
              (if In_Graph (H, U) and then In_Graph (H, V)
               then Reachable (H, U, V) = Reachable (G, U, V))));
      Lemma_Nb_Comp_Equiv (H, G);
   end Lemma_Covers_Same_Comp;

   procedure Property_Minimality (G, H : Graph) is
      T : constant Graph := Kruskal_Model (G);
   begin
      --  Same number of components : T Covers G (P2), H Covers G (Covers).
      Lemma_Kruskal_Same_Comp (G);
      Lemma_Covers_Same_Comp (H, G);
      pragma Assert (Nb_Components (T) = Nb_Components (H));

      --  Chain of minimality :
      --    weight (T) = Threshold_Sum (T, Max)      [Brick A : T is a forest]
      --             <= Threshold_Sum (H, Max)      [Brick B : greedy]
      --             <= weight (H).                [Brick A' : lower bound]
      Lemma_Weight_Is_Threshold_Sum (T);
      Lemma_Threshold_Sum_Greedy (G, H, Max_Weight);
      Lemma_Threshold_Sum_Lower_Bound (H);
   end Property_Minimality;

end Kruskal;
