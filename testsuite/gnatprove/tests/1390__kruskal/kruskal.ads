with Graphs; use Graphs;
with Integer_Lists; use Integer_Lists;
with Connectivity; use Connectivity;
with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;
--  Connectivity provides the Reachable model (proven equivalence relation).
--  The COMPUTED Connectivity goes through Path_Exists (Findable); we relate it to
--  Reachable via a bridge, in order to inherit symmetry/transitivity.


package Kruskal
  with SPARK_Mode => On
is
------------------------------------------------------------------------------
--  KRUSKAL_MODEL -- OVERVIEW OF THE FORMAL PROOF SCHEME
--
--  Kruskal_Model (G) builds a minimum-weight spanning forest of G by the usual
--  greedy method: enumerate every edge of G, sort them by ASCENDING weight, and
--  add each edge to the result unless its endpoints are already connected.
--
--  Four properties are proved about the result T = Kruskal_Model (G).  They are
--  the postcondition of Kruskal_Model (P1-P3) plus the standalone ghost lemma
--  Property_Minimality (P4).  All reasoning is done on the algebraic model
--  "Reachable" (a proved equivalence relation); it is bridged to the computed
--  connectivity "Connected" (depth-first search) so the properties also hold for
--  the executable notion.
--
--    P1  INCLUSION     Subgraph (T, G)               -- T uses only edges of G
--    P2  CONNECTIVITY  T spans G                      -- same connected components
--    P3  ACYCLICITY    Is_Forest (T)                  -- every edge is a bridge
--    P4  MINIMALITY    Total_Weight (T) <= Total_Weight (H)
--                                          for every spanning weighted subgraph H
--
--  P1, P2, P3 are CONSTRUCTION INVARIANTS: each is maintained by the main loop
--  (T only receives edges of G; every processed edge becomes connected in T;
--  an edge is added only between two not-yet-connected vertices, so no cycle is
--  ever created).
--
--============================================================================
--  P4 MINIMALITY -- THE THRESHOLD FORMULA
--============================================================================
--
--  Comparing two total weights directly is hard.  The key idea is to rewrite a
--  weight as a SUM OVER WEIGHT THRESHOLDS.  Let Restrict (F, s) be F with every
--  edge of length > s removed, and let nb_comp (.) be the number of connected
--  components (counted via representatives: the least vertex of each component).
--  Define, for a threshold bound N:
--
--      Threshold_Sum (F, N) = SUM over s = 0 .. N-1 of
--                                 ( nb_comp (Restrict (F, s)) - nb_comp (F) )
--
--  WHY THIS EQUALS THE WEIGHT (for a forest).  Each term counts "how many
--  component-merges are still missing at threshold s", i.e. the number of edges
--  whose weight is > s.  An edge of weight w is therefore counted once for each
--  s in 0 .. w-1, that is exactly w times.  Summing over all thresholds
--  reconstructs the total weight.  Because Weight is BOUNDED (1 .. Max_Weight),
--  the sum is finite and indexable by an Integer -- this is what makes the
--  formula formalizable.
--
--  The whole minimality proof is then the chain (T = Kruskal_Model (G)):
--
--      Total_Weight (T)  =   Threshold_Sum (T, Max_Weight)        -- (A)
--                        <=  Threshold_Sum (H, Max_Weight)        -- (B)
--                        <=  Total_Weight (H)                     -- (A')
--
--  BRICK (A)  Lemma_Weight_Is_Threshold_Sum -- for a FOREST the formula is an
--     EQUALITY.  Proved by induction on edge removal (variant: Total_Weight).
--     Removing a bridge {U,V} of length L raises nb_comp by exactly +1
--     (Lemma_Removal_Bridge_Component); via the commutation of Restrict with edge
--     removal, each threshold s < L loses exactly 1, i.e. -L overall for
--     Threshold_Sum -- matching the drop of Total_Weight.
--
--  BRICK (A') Lemma_Threshold_Sum_Lower_Bound -- for an ARBITRARY graph the
--     formula is a LOWER BOUND.  Same removal induction, but a removed edge is
--     either a bridge (+1, equality case) or redundant (Lemma_Removal_Non_Bridge:
--     nb_comp unchanged); in both cases the drop is <= L.
--
--  BRICK (B)  Lemma_Threshold_Sum_Greedy -- term by term,
--     nb_comp (Restrict (T, s)) <= nb_comp (Restrict (H, s))  and  nb_comp (T) =
--     nb_comp (H) (both are spanning).  This reduces to the GREEDY PROPERTY
--         nb_comp (Restrict (T, s)) = nb_comp (Restrict (G, s))
--     then <= nb_comp (Restrict (H, s)) by monotonicity (H is a subgraph of G).
--
--  THE GREEDY PROPERTY is FALSE for an arbitrary spanning forest -- it holds
--  only because Kruskal processes edges in ascending weight order.  It is
--  therefore proved INSIDE the construction loop: a ghost invariant states that
--  every processed edge is connected in the current result using only edges of
--  weight <= its own weight (tracked with the ghost Max_Seen_Weight, and relying
--  on Sort being proved to sort ascending).  This is exported as the loop's
--  postcondition, then lifted from edges to full reachability
--  (Lemma_Reachable_Via_Edges) and turned into the component count above
--  (Lemma_Nb_Comp_Reach).
--
--  ASSUMPTION ON H.  Property_Minimality requires H to be a WEIGHTED subgraph:
--  its edges carry the same lengths as in G.  Otherwise "thresholding by weight"
--  would be meaningless; this is the usual meaning of "subgraph" for a
--  minimum-weight problem.
--
------------------------------------------------------------------------------


   type Visited_Array is array (Vertex) of Boolean with Ghost;

   type Path is record
      Path_Found : Boolean;
      Traversal : List ;
      end record with Ghost;

   procedure lemma_equality_implies_same_list_in_graph (L1,L2: access constant Cell; G: Graph) with Ghost,
     Subprogram_Variant => (Structural => L1),
     Pre => (Equal(L1,L2) and then list_in_graph(L1,G)),
     Post => (list_in_graph(L2,G));

   procedure lemma_keeps_connected_component_add_vertex_list (L : access constant Cell; G:Graph) with Ghost,
     Pre => (L/=null and then L.Next /= null and then list_in_graph (L.Next,G) and then L.Value in 1 .. G.Size
             and then  Has_Edge (G, L.Value, L.Next.Value)),
     Post => (list_in_graph( L,G));



   procedure Lemma_One_Visited_Less (i : Positive; Old_Arr, New_Arr : Visited_Array; Target : Vertex)
   with Ghost,
        Pre => i <= Old_Arr'Last + 1
               and then not Old_Arr (Target)
               and then New_Arr (Target)
               and then (for all k in Vertex => (if k /= Target then Old_Arr(k) = New_Arr(k))),

        Post => (if i <= Target then
                    not_visited (i, New_Arr) = not_visited (i, Old_Arr) - 1
                 else
                    not_visited (i, New_Arr) = not_visited (i, Old_Arr)),
        Subprogram_Variant => (Increases => i);


function not_visited (i : Positive; V : Visited_Array) return Natural is
   (if i > V'Last then
      0
    elsif not V(i) then
      1 + not_visited (i + 1, V)
    else
      not_visited (i + 1, V))
with Ghost,
       Pre => i <= V'Last + 1,
       Post => (not_visited'Result <= V'Last - i + 1),
       Subprogram_Variant => (Increases => i);


   function list_in_graph (L : access constant Cell; G : Graph)
     return Boolean
   is
     (if L = null then
         True
      elsif L.Next = null then
         L.Value in 1 .. G.Size
      else
         L.Value in 1 .. G.Size
         and then L.Next.Value in 1 .. G.Size
         and then Has_Edge (G, L.Value, L.Next.Value)
         and then list_in_graph (L.Next, G))
   with Ghost, Subprogram_Variant => (Structural => L);


   ---------------------------------------------------------------------------
   --  Predicates on traversals, to express the COMPLETENESS of the search.
   ---------------------------------------------------------------------------

   --  All Nodes of L are Nodes of G that are NOT yet
   --  visited.  (The guard L.Value in 1 .. G.Size allows indexing
   --  Visited without range check.)
   function path_avoids (L : access constant Cell; Visited : Visited_Array; G : Graph)
     return Boolean
   is
     (L = null
      or else (L.Value in 1 .. G.Size
               and then not Visited (L.Value)
               and then path_avoids (L.Next, Visited, G)))
   with Ghost, Subprogram_Variant => (Structural => L);

   --  L never passes twice through the same Node.
   function simple_path (L : access constant Cell) return Boolean is
     (L = null
      or else (not Contains (L.Next, L.Value) and then simple_path (L.Next)))
   with Ghost, Subprogram_Variant => (Structural => L);

   --  Mark a Node Target ABSENT from L preserves the fact that L avoids the
   --  visited ones (induction on L).
   procedure lemma_avoid_add
     (L : access constant Cell; Visited, Visited2 : Visited_Array;
      Target : Vertex; G : Graph)
     with Ghost,
          Pre  => path_avoids (L, Visited, G)
                  and then not Contains (L, Target)
                  and then (for all k in Vertex =>
                              (if k /= Target then Visited (k) = Visited2 (k)))
                  and then Visited2 (Target),
          Post => path_avoids (L, Visited2, G),
          Subprogram_Variant => (Structural => L);

   --  The last Node of a valid Path is a Node of the graph.
   procedure lemma_last_elem_in_graph (L : access constant Cell; G : Graph)
     with Ghost,
          Pre  => L /= null and then list_in_graph (L, G),
          Post => Last_elem (L) in 1 .. G.Size,
          Subprogram_Variant => (Structural => L);

   --  A valid Path avoids any empty set of visited (no Node
   --  marked).
   procedure lemma_list_avoid_empty
     (L : access constant Cell; Visited : Visited_Array; G : Graph)
     with Ghost,
          Pre  => list_in_graph (L, G)
                  and then (for all k in Vertex => not Visited (k)),
          Post => path_avoids (L, Visited, G),
          Subprogram_Variant => (Structural => L);


   --  Visited with the Node S additionally marked.
   function Update_Visited (Visited : Visited_Array; S : Vertex) return Visited_Array
   is
     ([for K in Vertex => (if K = S then True else Visited (K))])
   with Ghost;

   --  The empty set of visited (no Node marked).  NAMED term (and not a
   --  repeated aggregate) to stay the same term everywhere and avoid
   --  array rewrites on the prover side.
   function No_Vertex_Visited return Visited_Array is
     ([for K in Vertex => False])
   with Ghost;

   --  Witness-FREE MODEL of the search.  Findable exactly mirrors the logic
   --  of Path_Exists: From_Idx Start, Target Target, avoiding the Visited.  Its
   --  post-condition is its defining equation (recursive function, variant
   --  not_visited).  It is this object that FIXES the Result_G of the search
   --  independently of the Witness.
   function Findable
     (G : Graph; Start, Target : Vertex; Visited : Visited_Array)
      return Boolean
   with Ghost,
        Pre  => In_Graph (G, Start) and then In_Graph (G, Target),
        Subprogram_Variant => (Decreases => not_visited (1, Visited)),
        Post => Findable'Result =
          (Start = Target
           or else (not Visited (Start)
                    and then (for some W in Vertex =>
                                W <= G.Size and then Has_Edge (G, W, Start)
                                and then Findable
                                           (G, W, Target,
                                            Update_Visited (Visited, Start)))));


   procedure Path_Exists
     (G               : Graph;
      Begin_V : Vertex;
      Target          : Vertex;
      Current_Vertex  : Vertex;
      Visited         : Visited_Array;
      Path_Walked : in out Path;
      Witness          : access constant Cell)
     with Ghost,
       Always_Terminates => True,
          Subprogram_Variant => (Decreases => not_visited (Visited'First, Visited)),
   --  The current Node is the head of the Traversal list

     --  (Path_Walked.Traversal.Value), so Traversal must be non-empty.  We
     --  also pass it as the IMMUTABLE parameter Current_Vertex: thus the
     --  Witness-free completeness can be expressed on it (stable even if Traversal
     --  changes).  Witness (ghost) is a candidate Path From_Idx the current Node:
     --  when it is provided, its head must coincide with the current Node.

     Pre =>

       not Path_Walked.Path_Found
       and then Path_Walked.Traversal /= null
       and then Last_elem(Path_Walked.Traversal) = Begin_V
     and then In_Graph (G, Target)
     and then Current_Vertex = Path_Walked.Traversal.Value
     and then list_in_graph (Path_Walked.Traversal, G)
     and then (if Witness /= null then Witness.Value = Path_Walked.Traversal.Value),
       Post =>

       --  The list stays valid, non-empty, and its last element stays the
       --  Node of Start (Push keeps the tail).  If a Path is Found,
       --  its head is the Target.


       list_in_graph (Path_Walked.Traversal, G)
       and then Path_Walked.Traversal /= null
       and then Last_elem (Path_Walked.Traversal) = Begin_V
       and then (if Path_Walked.Path_Found
                   then Path_Walked.Traversal.Value = Target)

       --  COMPLETENESS: if Witness is a simple and valid Path, from the current
       --  Node (its head) up to Target, avoiding the Nodes already visited,
       --  then the search necessarily succeeds.

       and then (if Witness /= null
                    and then list_in_graph (Witness, G)
                    and then Last_elem (Witness) = Target
                    and then path_avoids (Witness, Visited, G)
                    and then simple_path (Witness)
                 then Path_Walked.Path_Found)

       --  Witness-FREE COMPLETENESS: the Result_G is FIXED by the Findable model.
       --  On failure, the Target is not Findable From_Idx the current Node while
       --  avoiding Visited -- so there exists no Path.  (The traversal is
       --  unchanged on failure, its head stays the current Node.)

       and then (if not Path_Walked.Path_Found
                 then not Findable (G, Current_Vertex, Target, Visited))

       --  CORRECTNESS (reverse direction): on success, the Target IS Findable.
       --  With the previous clause, we thus have Path_Found = Findable.

       and then (if Path_Walked.Path_Found
                 then Findable (G, Current_Vertex, Target, Visited));



   procedure lemma_path_completeness (Traversal : access constant Cell; G : Graph)
     with Ghost,
          Pre => Traversal /= null
                 and then list_in_graph (Traversal, G)
                 and then simple_path (Traversal);


   function Same_Component
     (G : Graph; V : Vertex; U : Vertex;
      Witness : access constant Cell := null) Return Path
     with Ghost,
     Pre => In_Graph (G, V) and then In_Graph (G, U)
            and then (if Witness /= null then Witness.Value = V),
     --  We expose EVERYTHING that Path_Exists guarantees (called with Begin_V=V,
     --  Target=U):
     --    * the returned traversal is non-empty,
     --    * it is a valid list of the graph (real edges, valid Nodes),
     --    * its last element is the Node of Start V,
     --    * if a Connection is found, its head is the Target Node U
     --      (so V and U are in the same component, Witness = this Path),
     --    * COMPLETENESS: if we provide a valid simple Path from V (its head) to U
     --      as Witness, then the search succeeds (propagates the completeness
     --      clause of Path_Exists, with empty Visited).
     Post =>
       Same_Component'Result.Traversal /= null
       and then list_in_graph (Same_Component'Result.Traversal, G)
       and then Last_elem (Same_Component'Result.Traversal) = V
       and then (if Same_Component'Result.Path_Found
                 then Same_Component'Result.Traversal.Value = U)
       and then (if Witness /= null
                    and then list_in_graph (Witness, G)
                    and then Last_elem (Witness) = U
                    and then simple_path (Witness)
                 then Same_Component'Result.Path_Found)

       --  COMPLETE CHARACTERIZATION (propagated from Path_Exists): Path_Found
       --  is equivalent to the findability of U From_Idx V (without prior visit).
       and then (if not Same_Component'Result.Path_Found
                 then not Findable (G, V, U, No_Vertex_Visited))
       and then (if Same_Component'Result.Path_Found
                 then Findable (G, V, U, No_Vertex_Visited))
   ;

   --function kruskal(G:Graph) return Graph ;

   ---------------------------------------------------------------------------
   --  BOOLEAN Connectivity
   --
   --  Boolean wrapper of the Connectivity decided by Path_Exists: U and V
   --  are Are_Conn in G iff Same_Component Found a Path there.  The allocated
   --  Witness list is immediately freed, so the function is pure (no
   --  observable side effect) and usable in contract quantifiers.
   ---------------------------------------------------------------------------

   function Connected (G : Graph; U, V : Vertex) return Boolean is
     (Findable (G, U, V, No_Vertex_Visited))
   with Ghost, Pre => In_Graph (G, U) and then In_Graph (G, V);

   --  Reflexivity: every Node is Connected to itself.
   procedure Lemma_Connected_Reflexive (G : Graph; U : Vertex) with Ghost,
     Pre  => In_Graph (G, U),
     Post => Connected (G, U, U);

   --  An edge Connected its endpoints.
   procedure Lemma_Connected_Edge (G : Graph; U, V : Vertex) with Ghost,
     Pre  => In_Graph (G, U) and then In_Graph (G, V)
             and then Has_Edge (G, U, V),
     Post => Connected (G, U, V);

   --  BRIDGE, easy direction: what is Findable (DFS model) is Reachable
   --  (closure model).  Proven by induction on Findable, reusing
   --  reflexivity / edge / symmetry / transitivity already proven on Reachable.
   procedure Lemma_Findable_To_Reachable
     (G : Graph; U, V : Vertex; Visited : Visited_Array)
     with Ghost,
          Pre  => In_Graph (G, U) and then In_Graph (G, V)
                  and then Findable (G, U, V, Visited),
          Post => Reachable (G, U, V),
          Subprogram_Variant => (Decreases => not_visited (1, Visited));

   procedure Lemma_Connected_To_Reachable (G : Graph; U, V : Vertex)
     with Ghost,
          Pre  => In_Graph (G, U) and then In_Graph (G, V)
                  and then Connected (G, U, V),
          Post => Reachable (G, U, V);

   --  BRIDGE, HARD direction (traversal completeness): what is reached by the
   --  closure AVOIDING the Forbidden Nodes is Findable by the depth-first
   --  traversal that avoids those same Nodes.  Proven by induction on the
   --  number of unvisited Nodes (like Findable), by peeling the FIRST step
   --  (Lemma_First_Step of Connectivity).
   procedure Lemma_Avoiding_Closure_To_Findable
     (G : Graph; Start, Target : Vertex; Forbidden : Visited_Array)
     with Ghost,
          Pre  => In_Graph (G, Start) and then In_Graph (G, Target)
                  and then not Forbidden (Start)
                  and then Avoiding_Closure
                             (G, Singleton (Start),
                              Vertex_Set (Forbidden), G.Size) (Target),
          Post => Findable (G, Start, Target, Forbidden),
          Subprogram_Variant => (Decreases => not_visited (1, Forbidden));

   --  BRIDGE, full reverse direction: Reachable => Connected.  With
   --  Lemma_Connected_To_Reachable, this closes the equivalence
   --  Reachable <=> Connected, so the COMPUTED Connectivity (Path_Exists)
   --  coincides with the model.
   procedure Lemma_Reachable_To_Connected (G : Graph; U, V : Vertex)
     with Ghost,
          Pre  => In_Graph (G, U) and then In_Graph (G, V)
                  and then Reachable (G, U, V),
          Post => Connected (G, U, V);


   ---------------------------------------------------------------------------
   --  PROPERTY 1: INCLUSION (subgraph)
   --
   --  The Result_G graph is a subgraph of the Origin graph: same Nodes
   --  (same sizes), and every edge of the Result_G is an edge of the Origin.
   --
   --  The equality of sizes is the first conjunct, established via "and then", so
   --  that the calls Has_Edge (Result_Graph, .) are well-formed:
   --  In_Graph (Result_Graph, .) then follows from In_Graph (Origin_Graph, .).
   ---------------------------------------------------------------------------

   function Subgraph (Result_Graph, Origin_Graph : Graph) return Boolean
   is
     (Result_Graph.Size = Origin_Graph.Size
      and then
        (for all Node_A in Vertex =>
           (for all Node_B in Vertex =>
              (if Node_A <= Origin_Graph.Size
                  and then Node_B <= Origin_Graph.Size
                  and then Has_Edge (Result_Graph, Node_A, Node_B)
               then Has_Edge (Origin_Graph, Node_A, Node_B)))))
   with Ghost;

   --  FRAME: adding to a subgraph an edge already present in the large
   --  graph preserves the subgraph relation.  ISOLATED lemma (small context),
   --  so that the proof of the frame stays light in memory even under heavy
   --  parallelization (unlike the in-Row assertion in Kruskal_Model,
   --  which carries the whole context of the loop).
   procedure Lemma_Add_Subgraph
     (Before, After, Grand : Graph; U0, V0 : Vertex)
     with Ghost,
       Pre  => Before.Size = Grand.Size and then After.Size = Grand.Size
               and then In_Graph (Grand, U0) and then In_Graph (Grand, V0)
               and then Same_Except (After, Before, U0, V0)
               and then Has_Edge (Grand, U0, V0)
               and then Subgraph (Before, Grand),
       Post => Subgraph (After, Grand);

   --  FRAME: adding an edge to a graph INCLUDES the Old_Arr graph in the
   --  New_Arr (every prior edge subsists).  ISOLATED lemma (small context).
   procedure Lemma_Add_Edges_Included
     (Before, After : Graph; U0, V0 : Vertex)
     with Ghost,
       Pre  => Before.Size = After.Size
               and then In_Graph (Before, U0) and then In_Graph (Before, V0)
               and then Same_Except (After, Before, U0, V0)
               and then Has_Edge (After, U0, V0),
       Post => Edges_Included (Before, After);


   --  The graph deprived of the edge {U, V}.  (Declared before Kruskal_Model because its
   --  acyclicity post-condition is expressed with Is_Forest / Without_Edge.)
   function Without_Edge (G : Graph; U, V : Vertex) return Graph
     with Ghost,
       Pre  => In_Graph (G, U) and then In_Graph (G, V),
       Post => Without_Edge'Result.Size = G.Size
               and then not Has_Edge (Without_Edge'Result, U, V)
               and then not Has_Edge (Without_Edge'Result, V, U)
               and then Same_Except (Without_Edge'Result, G, U, V);

   --  "The edge {A, B} is a BRIDGE of G": removing it disconnects A and B.  OPAQUE
   --  (defining post): the costly term not Reachable (Without_Edge ...)
   --  is thus hidden behind an abstract boolean, which keeps LIGHT the
   --  quantifiers of Is_Forest and of the invariant of Lemma_Forest_Add.
   function Is_Bridge (G : Graph; A, B : Vertex) return Boolean
     with Ghost,
       Pre  => In_Graph (G, A) and then In_Graph (G, B),
       --  TRIVIALLY true on the diagonal (A = B): thus the self-loop case of the
       --  invariants requires NO reasoning (no expansion of Reachable).
       --  Without effect on the meaning: an edge always satisfies A /= B.
       Post => Is_Bridge'Result =
         (A = B or else not Reachable (Without_Edge (G, A, B), A, B));

   --  G is a FOREST: every edge is a bridge (removing it disconnects its
   --  endpoints).  OPAQUE (defining post) so as not to weigh down the other VC.
   function Is_Forest (G : Graph) return Boolean
     with Ghost,
       Post => Is_Forest'Result =
         (for all A in Vertex =>
            (for all B in Vertex =>
               (if In_Graph (G, A) and then In_Graph (G, B)
                   and then Has_Edge (G, A, B)
                then Is_Bridge (G, A, B))));

   --  BRIDGE REMOVAL (P4): removing a BRIDGE-edge {U,V} increases the number
   --  of components by EXACTLY 1 (the components of U and of V, disjoint
   --  after removal, merge through the edge).  Holds for an ARBITRARY graph
   --  as soon as {U,V} is a bridge (Is_Bridge) -- in particular for every
   --  edge of a forest.  Key of "forest: |edges| = n - nb_comp".
   procedure Lemma_Removal_Bridge_Component (F : Graph; U, V : Vertex)
     with Ghost,
       Pre  => In_Graph (F, U) and then In_Graph (F, V) and then U < V
               and then Has_Edge (F, U, V) and then Is_Bridge (F, U, V),
       Post => Nb_Components (Without_Edge (F, U, V)) = Nb_Components (F) + 1;

   --  NON-BRIDGE EDGE REMOVAL (P4): removing an edge {U,V} that is NOT
   --  a bridge (U and V stay reachable without it) does NOT change the number of
   --  components.  With Lemma_Removal_Bridge_Component, bounds the removal of an
   --  arbitrary edge: nb_comp increases by 0 (non-bridge) or 1 (bridge).
   procedure Lemma_Removal_Non_Bridge (F : Graph; U, V : Vertex)
     with Ghost,
       Pre  => In_Graph (F, U) and then In_Graph (F, V) and then U < V
               and then not Is_Bridge (F, U, V),
       Post => Nb_Components (Without_Edge (F, U, V)) = Nb_Components (F);

   --  Without_Edge preserves the inclusion of edges.
   procedure Lemma_Without_Edge_Monotone (H, F : Graph; U, V : Vertex)
     with Ghost,
       Pre  => Edges_Included (H, F)
               and then In_Graph (F, U) and then In_Graph (F, V),
       Post => Edges_Included (Without_Edge (H, U, V), Without_Edge (F, U, V));

   --  SUBFOREST: a subgraph of a forest is a forest (fewer edges, the
   --  bridges stay so).  Serves for "Restrict (F, s) is a forest".
   procedure Lemma_Subforest (H, F : Graph)
     with Ghost,
       Pre  => Is_Forest (F) and then Edges_Included (H, F),
       Post => Is_Forest (H);

   function Kruskal_Model (G : Graph) return Graph with Ghost,
     Post => Subgraph (Kruskal_Model'Result, G)
             --  Property 2, direction ⇒ (spanning): every edge of G has its
             --  endpoints connected in the Result_G.  With the direction ⇐
             --  (Property_Connectivity_Inclusion), this gives the equality of the
             --  connected components of G and of the Result_G.
             and then Edges_Connected (G, Kruskal_Model'Result)
             --  Property 3 (acyclicity): the Result_G is a forest.
             and then Is_Forest (Kruskal_Model'Result)
             --  GREEDY (basis of P4 minimality): every edge of G has its
             --  endpoints linked in the Result_G using only
             --  edges of weight <= its own weight (Kruskal processes the edges
             --  by ascending weight).
             and then
               (for all U in Vertex =>
                  (for all V in Vertex =>
                     (if In_Graph (G, U) and then In_Graph (G, V)
                         and then Has_Edge (G, U, V)
                      then Reachable
                             (Restrict
                                (Kruskal_Model'Result, Edge_Length (G, U, V)),
                              U, V))));


   ---------------------------------------------------------------------------
   --  PROPERTY 2: Connectivity (spanning graph)
   --
   --  Two Nodes are Are_Conn (Reachable) in the Result_G IFF they are so
   --  in G.  Reachable is the proven realization of the
   --  Same_Connected_Component predicate; Connected (= Path_Exists) is related to it by the
   --  easy bridge.
   --
   --  INCLUSION direction (⇐): the Result_G being a subgraph of G (property 1),
   --  every Connection of the Result_G already exists in G.
   ---------------------------------------------------------------------------

   procedure Property_Connectivity_Inclusion (G : Graph) with Ghost,
     Post =>
       (for all Vertex_U in Vertex =>
          (for all Vertex_V in Vertex =>
             (if In_Graph (G, Vertex_U) and then In_Graph (G, Vertex_V)
                 and then Reachable (Kruskal_Model (G), Vertex_U, Vertex_V)
              then Reachable (G, Vertex_U, Vertex_V))));

   --  PROPERTY 2, COMPLETE STATEMENT (in the sense of the Reachable model): G and the
   --  Result_G have exactly the SAME connected components (equivalence in
   --  both directions).  It is the "spanning graph" property of the document.
   procedure Property_Connectivity (G : Graph) with Ghost,
     Post =>
       (for all Vertex_U in Vertex =>
          (for all Vertex_V in Vertex =>
             (if In_Graph (G, Vertex_U) and then In_Graph (G, Vertex_V)
              then Reachable (Kruskal_Model (G), Vertex_U, Vertex_V)
                   = Reachable (G, Vertex_U, Vertex_V))));

   --  PROPERTY 2, in the sense of the project's REAL Connectivity: Connected
   --  (= Path_Exists).  It is the final "spanning graph" statement in terms of the
   --  COMPUTED Connectivity, not the model.  It follows from the Reachable version
   --  above and from the equivalence Reachable <=> Connected (the two bridges).
   procedure Property_Connectivity_Real (G : Graph) with Ghost,
     Post =>
       (for all Vertex_U in Vertex =>
          (for all Vertex_V in Vertex =>
             (if In_Graph (G, Vertex_U) and then In_Graph (G, Vertex_V)
              then Connected (Kruskal_Model (G), Vertex_U, Vertex_V)
                   = Connected (G, Vertex_U, Vertex_V))));

   ---------------------------------------------------------------------------
   --  PROPERTY 3: ACYCLICITY (forest)
   ---------------------------------------------------------------------------

   --  A graph without edge is a forest.
   procedure Lemma_Forest_Empty (G : Graph) with Ghost,
     Pre  => (for all A in Vertex =>
                (for all B in Vertex =>
                   (if In_Graph (G, A) and then In_Graph (G, B)
                    then not Has_Edge (G, A, B)))),
     Post => Is_Forest (G);

   --  NO INDUCTION: adding the edge {U0, V0} between two NOT Are_Conn Nodes
   --  preserves the forest.  (Core: the decomposition lemma.)
   procedure Lemma_Forest_Add
     (G_Before, G_After : Graph; U0, V0 : Vertex)
     with Ghost,
       Pre  => G_Before.Size = G_After.Size
               and then In_Graph (G_Before, U0) and then In_Graph (G_Before, V0)
               and then Same_Except (G_After, G_Before, U0, V0)
               and then Has_Edge (G_After, U0, V0)
               and then not Reachable (G_Before, U0, V0)
               and then Is_Forest (G_Before),
       Post => Is_Forest (G_After);

   --  ACYCLICITY (in the sense of the Reachable model): for every edge (U, V) of the
   --  Result_G, removing it DISCONNECTS U and V (every edge is a bridge, the
   --  Result_G is a forest).  Follows directly from Is_Forest (Result_G).
   procedure Property_Acyclicity (G : Graph) with Ghost,
     Post =>
       (for all Vertex_U in Vertex =>
          (for all Vertex_V in Vertex =>
             (if In_Graph (G, Vertex_U) and then In_Graph (G, Vertex_V)
                 and then Has_Edge (Kruskal_Model (G), Vertex_U, Vertex_V)
              then not Reachable
                     (Without_Edge (Kruskal_Model (G), Vertex_U, Vertex_V),
                      Vertex_U, Vertex_V))));

   --  ACYCLICITY in the sense of the REAL Connectivity (Connected = Path_Exists):
   --  removing any edge of the Result_G disconnects (in the computed sense)
   --  its endpoints.  Follows from the Reachable version + bridge
   --  Connected => Reachable (contrapositive: not Reachable => not Connected).
   procedure Property_Acyclicity_Real (G : Graph) with Ghost,
     Post =>
       (for all Vertex_U in Vertex =>
          (for all Vertex_V in Vertex =>
             (if In_Graph (G, Vertex_U) and then In_Graph (G, Vertex_V)
                 and then Has_Edge (Kruskal_Model (G), Vertex_U, Vertex_V)
              then not Connected
                     (Without_Edge (Kruskal_Model (G), Vertex_U, Vertex_V),
                      Vertex_U, Vertex_V))));

   ---------------------------------------------------------------------------
   --  PROPERTY 4: WEIGHT MINIMALITY (Optimality)
   --
   --  The document leaves the statement blank.  We formalize it as the standard
   --  OPTIMALITY of a minimum weight spanning tree/forest (MST/MSF): among
   --  ALL the subgraphs of G that preserve the Connectivity (same
   --  connected components as G, in the real Connected sense), Kruskal's
   --  Result_G has the MINIMAL total weight.
   --
   --  Total weight = sum of the lengths (Edge_Length) of all the edges, in
   --  Big_Natural (unbounded mathematical integer: no overflow).
   ---------------------------------------------------------------------------

   --  Contribution (weight) of the canonical cell (A, B): Edge_Length if
   --  the edge {A, B} exists and A < B (canonical count only once), 0 otherwise.
   function Contrib (G : Graph; A : Vertex; B : Positive) return Big_Natural is
     (if A <= G.Size and then B <= G.Size and then A < B
         and then Has_Edge (G, A, B)
      then To_Big_Integer (Integer (Edge_Length (G, A, B)))
      else 0)
   with Ghost, Pre => B <= Max_Vertices + 1;

   --  Sum of the lengths of the canonical edges {A, B} with B ranging over
   --  Column .. G.Size (edge counted only once since we impose A < B).
   function Weight_Columns
     (G : Graph; A : Vertex; Column : Positive) return Big_Natural
   is
     (if Column > G.Size then 0
      else Contrib (G, A, Column) + Weight_Columns (G, A, Column + 1))
   with Ghost,
        Pre => In_Graph (G, A) and then Column <= Max_Vertices + 1,
        Subprogram_Variant => (Increases => Column);

   --  Sum of the weights of the rows Row .. G.Size.
   function Weight_Rows (G : Graph; Row : Positive) return Big_Natural is
     (if Row > G.Size then 0
      else Weight_Columns (G, Row, 1) + Weight_Rows (G, Row + 1))
   with Ghost,
        Pre => Row <= Max_Vertices + 1,
        Subprogram_Variant => (Increases => Row);

   --  Total weight of the graph (sum of all the edge lengths).
   function Total_Weight (G : Graph) return Big_Natural is
     (Weight_Rows (G, 1))
   with Ghost;

   ---------------------------------------------------------------------------
   --  Weight decomposition: removing an edge decreases the total weight by its
   --  length.  Sequence of lemmas by induction on the structure of the sum.
   ---------------------------------------------------------------------------

   --  Row congruence: if the Row A has the SAME contributions in K and G
   --  (columns >= C), the column sums coincide.
   procedure Lemma_Columns_Cong (K, G : Graph; A : Vertex; C : Positive)
     with Ghost,
       Pre  => K.Size = G.Size and then In_Graph (G, A)
               and then C <= Max_Vertices + 1
               and then (for all B in 1 .. Max_Vertices + 1 =>
                           (if C <= B then Contrib (K, A, B) = Contrib (G, A, B))),
       Post => Weight_Columns (K, A, C) = Weight_Columns (G, A, C),
       Subprogram_Variant => (Increases => C);

   --  Row U: K and G differ only at the Column V (V > U).  The column sum
   --  then differs exactly by the contribution of the cell (U, V).
   --  ADDITIVE formula (no subtraction: we stay in Big_Natural).
   procedure Lemma_Columns_Diff (K, G : Graph; U, V : Vertex; C : Positive)
     with Ghost,
       Pre  => K.Size = G.Size and then In_Graph (G, U) and then U < V
               and then V <= G.Size and then C <= Max_Vertices + 1
               and then (for all B in 1 .. Max_Vertices + 1 =>
                           (if C <= B and then B /= V
                            then Contrib (K, U, B) = Contrib (G, U, B))),
       Post =>
         Weight_Columns (G, U, C)
           + (if C <= V then Contrib (K, U, V) else 0)
         = Weight_Columns (K, U, C)
           + (if C <= V then Contrib (G, U, V) else 0),
       Subprogram_Variant => (Increases => C);

   --  Row sums: K and G differ only at the cell (U, V).
   procedure Lemma_Rows_Diff (K, G : Graph; U, V : Vertex; L : Positive)
     with Ghost,
       Pre  => K.Size = G.Size and then In_Graph (G, U) and then U < V
               and then V <= G.Size and then L <= Max_Vertices + 1
               --  Rows A /= U: equal contributions.
               and then (for all A in 1 .. Max_Vertices =>
                           (if L <= A and then A /= U then
                              (for all B in 1 .. Max_Vertices + 1 =>
                                 Contrib (K, A, B) = Contrib (G, A, B))))
               --  Row U: equal except Column V.
               and then (for all B in 1 .. Max_Vertices + 1 =>
                           (if B /= V
                            then Contrib (K, U, B) = Contrib (G, U, B))),
       Post =>
         Weight_Rows (G, L) + (if L <= U then Contrib (K, U, V) else 0)
         = Weight_Rows (K, L) + (if L <= U then Contrib (G, U, V) else 0),
       Subprogram_Variant => (Increases => L);

   --  EDGE REMOVAL: Total_Weight (G) = Total_Weight (G without {U,V}) + length.
   procedure Lemma_Weight_Removal (G : Graph; U, V : Vertex)
     with Ghost,
       Pre  => In_Graph (G, U) and then In_Graph (G, V) and then U < V,
       Post => Total_Weight (G)
               = Total_Weight (Without_Edge (G, U, V)) + Contrib (G, U, V);

   --  THRESHOLD SUM: Σ_{s=0}^{N-1} (Nb_Components (Restrict (F, s)) -
   --  Nb_Components (F)).  Each term is >= 0 (Restrict (F, s) is a
   --  subgraph of F, so AT LEAST as many components -- monotonicity).
   --  Key of minimality: for a FOREST, with N > every weight, this sum
   --  EQUALS the total weight (threshold identity); for an ARBITRARY graph it
   --  LOWER-BOUNDS it.  Since Max_Weight upper-bounds every weight, Threshold_Sum (F, Max_Weight)
   --  is the complete sum.
   function Threshold_Sum (F : Graph; N : Weight_Threshold) return Big_Integer is
     (if N = 0 then To_Big_Integer (0)
      else Threshold_Sum (F, N - 1)
           + (To_Big_Integer (Nb_Components (Restrict (F, N - 1)))
              - To_Big_Integer (Nb_Components (F))))
   with Ghost,
        Subprogram_Variant => (Decreases => N);

   --  COMMUTATION Threshold / removal: thresholding THEN removing {U,V}, or removing
   --  THEN thresholding, produces the SAME set of edges (those of F with length
   --  <= S, deprived of {U,V}) -- so the same number of components.
   procedure Lemma_Restrict_Without_Edge
     (F : Graph; U, V : Vertex; S : Weight_Threshold)
     with Ghost,
       Pre  => In_Graph (F, U) and then In_Graph (F, V),
       Post => Nb_Components (Restrict (Without_Edge (F, U, V), S))
               = Nb_Components (Without_Edge (Restrict (F, S), U, V));

   --  The thresholded graph is a SUB-graph: its edges are included in G.
   procedure Lemma_Restrict_Included (G : Graph; S : Weight_Threshold)
     with Ghost,
       Post => Edges_Included (Restrict (G, S), G);

   --  Threshold monotonicity: thresholding lower gives fewer edges.
   procedure Lemma_Restrict_Threshold_Monotone (G : Graph; W, S : Weight_Threshold)
     with Ghost,
       Pre  => W <= S,
       Post => Edges_Included (Restrict (G, W), Restrict (G, S));

   --  A WEIGHTED subgraph (same lengths on its edges) stays a subgraph
   --  after thresholding.
   procedure Lemma_Restrict_Subgraph (H, G : Graph; S : Weight_Threshold)
     with Ghost,
       Pre  => Subgraph (H, G)
               and then (for all A in Vertex =>
                           (for all B in Vertex =>
                              (if A <= G.Size and then B <= G.Size
                                  and then Has_Edge (H, A, B)
                               then Edge_Length (H, A, B)
                                    = Edge_Length (G, A, B)))),
       Post => Edges_Included (Restrict (H, S), Restrict (G, S));

   --  Removing an edge only subtracts: edges included in G.
   procedure Lemma_Without_Edge_Included (G : Graph; U, V : Vertex)
     with Ghost,
       Pre  => In_Graph (G, U) and then In_Graph (G, V),
       Post => Edges_Included (Without_Edge (G, U, V), G);

   --  ADDITION AND Threshold: adding an edge (at an empty slot) preserves
   --  the thresholded reachability of the already linked pairs.  Serves for maintaining
   --  the greedy invariant of Kruskal_Model (case "edge added").
   procedure Lemma_Restrict_Add
     (G_Av, G_Ap : Graph; U0, V0, X, Y : Vertex; S : Weight_Threshold)
     with Ghost,
       Pre  => G_Av.Size = G_Ap.Size
               and then In_Graph (G_Av, U0) and then In_Graph (G_Av, V0)
               and then Same_Except (G_Ap, G_Av, U0, V0)
               and then not Has_Edge (G_Av, U0, V0)
               and then In_Graph (G_Av, X) and then In_Graph (G_Av, Y)
               and then Reachable (Restrict (G_Av, S), X, Y),
       Post => Reachable (Restrict (G_Ap, S), X, Y);

   --  Threshold ABOVE THE MAX: if all the edges of G have a weight <= S,
   --  Restrict (G, S) keeps all the edges, so preserves the reachability.
   --  Serves for maintaining the greedy invariant (case "edge discarded").
   procedure Lemma_Restrict_Complete (G : Graph; S : Weight_Threshold; X, Y : Vertex)
     with Ghost,
       Pre  => In_Graph (G, X) and then In_Graph (G, Y)
               and then (for all A in Vertex =>
                           (for all B in Vertex =>
                              (if A <= G.Size and then B <= G.Size
                                  and then Has_Edge (G, A, B)
                               then Edge_Length (G, A, B) <= S)))
               and then Reachable (G, X, Y),
       Post => Reachable (Restrict (G, S), X, Y);

   --  Removing an ABSENT edge is a no-op: same number of components.
   procedure Lemma_Without_Edge_Absent (G : Graph; U, V : Vertex)
     with Ghost,
       Pre  => In_Graph (G, U) and then In_Graph (G, V)
               and then not Has_Edge (G, U, V),
       Post => Nb_Components (Without_Edge (G, U, V)) = Nb_Components (G);

   --  BRIDGE-EDGE REMOVAL AND THRESHOLD SUM: in a FOREST, removing
   --  the edge {U,V} (length L) decreases Threshold_Sum (_, N) by exactly
   --  min (L, N).  Each Threshold s < L loses one unit there (the edge separated two
   --  components there); the thresholds s >= L are unchanged.
   procedure Lemma_Threshold_Sum_Removal_Forest
     (F : Graph; U, V : Vertex; N : Weight_Threshold)
     with Ghost,
       Pre  => In_Graph (F, U) and then In_Graph (F, V) and then U < V
               and then Has_Edge (F, U, V) and then Is_Forest (F),
       Post => Threshold_Sum (F, N)
               = Threshold_Sum (Without_Edge (F, U, V), N)
                 + To_Big_Integer
                     (Integer'Min (Integer (Edge_Length (F, U, V)), N)),
       Subprogram_Variant => (Decreases => N);

   --  BASE CASE (graph WITHOUT edge): zero weight, Column by Column.
   procedure Lemma_Weight_Col_Empty (F : Graph; A : Vertex; C : Positive)
     with Ghost,
       Pre  => In_Graph (F, A) and then C <= Max_Vertices + 1
               and then (for all B in Vertex =>
                           (if C <= B and then A < B and then B <= F.Size
                            then not Has_Edge (F, A, B))),
       Post => Weight_Columns (F, A, C) = 0,
       Subprogram_Variant => (Increases => C);

   procedure Lemma_Weight_Row_Empty (F : Graph; L : Positive)
     with Ghost,
       Pre  => L <= Max_Vertices + 1
               and then (for all A in Vertex =>
                           (for all B in Vertex =>
                              (if A < B and then B <= F.Size
                               then not Has_Edge (F, A, B)))),
       Post => Weight_Rows (F, L) = 0,
       Subprogram_Variant => (Increases => L);

   --  BASE CASE: zero threshold sum (each Threshold keeps all the
   --  components since there is no edge to remove).
   procedure Lemma_Threshold_Sum_Empty (F : Graph; N : Weight_Threshold)
     with Ghost,
       Pre  => (for all A in Vertex =>
                  (for all B in Vertex =>
                     (if A < B and then B <= F.Size
                      then not Has_Edge (F, A, B)))),
       Post => Threshold_Sum (F, N) = 0,
       Subprogram_Variant => (Decreases => N);

   --  BRICK A: for a FOREST, the total weight EQUALS the complete threshold
   --  sum (threshold identity, by successive removal of the bridge-edges).
   procedure Lemma_Weight_Is_Threshold_Sum (F : Graph)
     with Ghost,
       Pre  => Is_Forest (F),
       Post => Total_Weight (F) = Threshold_Sum (F, Max_Weight),
       Subprogram_Variant => (Decreases => Total_Weight (F));

   --  BRICK A': for an ARBITRARY graph, removing an edge {U,V} (length
   --  L) decreases Threshold_Sum (_, N) by AT MOST min (L, N) -- equality if the edge
   --  is a bridge, strictly less otherwise (redundant edge).
   procedure Lemma_Threshold_Sum_Removal_Upper_Bound
     (H : Graph; U, V : Vertex; N : Weight_Threshold)
     with Ghost,
       Pre  => In_Graph (H, U) and then In_Graph (H, V) and then U < V
               and then Has_Edge (H, U, V),
       Post => Threshold_Sum (H, N)
               <= Threshold_Sum (Without_Edge (H, U, V), N)
                  + To_Big_Integer
                      (Integer'Min (Integer (Edge_Length (H, U, V)), N)),
       Subprogram_Variant => (Decreases => N);

   --  BRICK A' (consequence): for an arbitrary graph, the complete threshold
   --  sum LOWER-BOUNDS the total weight.
   procedure Lemma_Threshold_Sum_Lower_Bound (H : Graph)
     with Ghost,
       Post => Threshold_Sum (H, Max_Weight) <= Total_Weight (H),
       Subprogram_Variant => (Decreases => Total_Weight (H));

   --  GREEDY (P4): at each Threshold, Kruskal's Result_G has AT MOST as many
   --  components as G (it links everything G links with light edges).
   procedure Lemma_Greedy_Nb_Comp (G : Graph; S : Weight_Threshold)
     with Ghost,
       Post => Nb_Components (Restrict (Kruskal_Model (G), S))
               <= Nb_Components (Restrict (G, S));

   --  BRICK B: the threshold sum of Kruskal's Result_G LOWER-BOUNDS that of any
   --  spanning subgraph H (term by term: at each Threshold, T has at most as many
   --  components as H, and T and H have the same total number of components).
   procedure Lemma_Threshold_Sum_Greedy (G, H : Graph; N : Weight_Threshold)
     with Ghost,
       Pre  => Subgraph (H, G)
               and then (for all A in Vertex =>
                           (for all B in Vertex =>
                              (if A <= G.Size and then B <= G.Size
                                  and then Has_Edge (H, A, B)
                               then Edge_Length (H, A, B)
                                    = Edge_Length (G, A, B))))
               and then Nb_Components (Kruskal_Model (G)) = Nb_Components (H),
       Post => Threshold_Sum (Kruskal_Model (G), N) <= Threshold_Sum (H, N),
       Subprogram_Variant => (Decreases => N);

   --  H Covers G: same size, and same connected components (real
   --  Connectivity Connected) at every pair of Nodes.
   function Covers (H, G : Graph) return Boolean is
     (H.Size = G.Size
      and then
        (for all U in Vertex =>
           (for all V in Vertex =>
              (if In_Graph (G, U) and then In_Graph (G, V)
               then Connected (H, U, V) = Connected (G, U, V)))))
   with Ghost;

   --  MINIMALITY: among all the spanning subgraphs of G, Kruskal's Result_G
   --  is of minimal total weight.  (Since it is acyclic -- P3 -- and
   --  spanning -- P2 --, it is a minimum weight spanning tree/forest.)
   --  The "for every spanning subgraph H" is expressed by the universally
   --  quantified PARAMETER H (SPARK idiom: one cannot quantify over
   --  all the values of a type in a contract).
   --  Kruskal's Result_G has the same number of components as G (it is
   --  spanning: same reachability).
   procedure Lemma_Kruskal_Same_Comp (G : Graph)
     with Ghost,
       Post => Nb_Components (Kruskal_Model (G)) = Nb_Components (G);

   --  A SPANNING subgraph has the same number of components as G.
   procedure Lemma_Covers_Same_Comp (H, G : Graph)
     with Ghost,
       Pre  => Subgraph (H, G) and then Covers (H, G),
       Post => Nb_Components (H) = Nb_Components (G);

   procedure Property_Minimality (G, H : Graph) with Ghost,
     Pre  => Subgraph (H, G) and then Covers (H, G)
             --  H is a WEIGHTED subgraph: its edges carry the lengths
             --  of G (usual sense of "subgraph" for a weight problem).
             and then (for all A in Vertex =>
                         (for all B in Vertex =>
                            (if A <= G.Size and then B <= G.Size
                                and then Has_Edge (H, A, B)
                             then Edge_Length (H, A, B) = Edge_Length (G, A, B)))),
     Post => Total_Weight (Kruskal_Model (G)) <= Total_Weight (H);


end Kruskal;
