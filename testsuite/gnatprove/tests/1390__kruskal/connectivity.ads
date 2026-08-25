
with Graphs; use Graphs;

package Connectivity
  with SPARK_Mode => On, Ghost
is

   type Vertex_Set is array (Vertex) of Boolean;

   --  The set reduced to the single Node Source.

   function Singleton (Source : Vertex) return Vertex_Set is
     (for Node in Vertex => Node = Source);

   --  Set inclusion (point by point).

   function Included (Petit, Grand : Vertex_Set) return Boolean is
     (for all Node in Vertex => (if Petit (Node) then Grand (Node)));

   --  One closure step: the Nodes already Reached, plus every Neighbour (via an
   --  edge of G) of a reached Node.

   --  NB: a "normal" function (not an expression), hence OPAQUE to the prover
   --  outside its body: Extend (X) is seen as an abstract array,
   --  characterized component by component by its post-condition.  This avoids
   --  expanding the "for some Neighbour" quantifier in every array equality
   --  (Closure (X, 1) = Extend (X), etc.), which otherwise blows up the prover.

   function Extend (G : Graph; Reached : Vertex_Set)
     return Vertex_Set
     with Post =>
       (for all Node in Vertex =>
          Extend'Result (Node) =
            (Reached (Node)
             or else (Node <= G.Size
                      and then (for some Neighbour in Vertex =>
                                  Neighbour <= G.Size
                                  and then Reached (Neighbour)
                                  and then Has_Edge (G, Neighbour, Node)))));

   --  Iterated closure: Fuel propagation steps.

   function Closure (G : Graph; Reached : Vertex_Set; Fuel : Natural)
     return Vertex_Set
   is
     (if Fuel = 0 then Reached
      else Closure (G, Extend (G, Reached), Fuel - 1))
   with Subprogram_Variant => (Decreases => Fuel);

   --  Source and Target are in the same connected component of G.

   function Reachable (G : Graph; Source, Target : Vertex) return Boolean is
     (Closure (G, Singleton (Source), G.Size) (Target))
   with Pre => In_Graph (G, Source) and then In_Graph (G, Target);

   ---------------------------------------------------------------------------
   --  Basic lemmas: growth and monotonicity of the closure.
   ---------------------------------------------------------------------------

   procedure Lemma_Extend_Increasing (G : Graph; Reached : Vertex_Set)
     with Post => Included (Reached, Extend (G, Reached));

   procedure Lemma_Extend_Monotone
     (G : Graph; Petit, Grand : Vertex_Set)
     with Pre  => Included (Petit, Grand),
          Post => Included (Extend (G, Petit), Extend (G, Grand));

   procedure Lemma_Closure_Increasing
     (G : Graph; Reached : Vertex_Set; Fuel : Natural)
     with Post => Included (Reached, Closure (G, Reached, Fuel)),
          Subprogram_Variant => (Decreases => Fuel);

   procedure Lemma_Closure_Monotone
     (G : Graph; Petit, Grand : Vertex_Set; Fuel : Natural)
     with Pre  => Included (Petit, Grand),
          Post => Included (Closure (G, Petit, Fuel),
                          Closure (G, Grand, Fuel)),
          Subprogram_Variant => (Decreases => Fuel);

   --  The closure grows with the Fuel: one more step removes nothing.

   procedure Lemma_Closure_Fuel_Increasing
     (G : Graph; Reached : Vertex_Set; Fuel : Natural)
     with Pre  => Fuel <= Max_Vertices,
          Post => Included (Closure (G, Reached, Fuel),
                          Closure (G, Reached, Fuel + 1));

   --  Composition: two successive closures = a closure with cumulative
   --  Fuel.  (Closure applies Extend "Fuel" times.)

   procedure Lemma_Closure_Composition
     (G : Graph; Reached : Vertex_Set; N, M : Natural)
     with Pre  => N <= Max_Vertices and then M <= Max_Vertices,
          Post => Closure (G, Reached, N + M)
                  = Closure (G, Closure (G, Reached, N), M),
          Subprogram_Variant => (Decreases => N);

   --  One closure step = one Extend step (explicit unrolling, to avoid
   --  the prover expanding Extend's quantifier inside an equality).

   procedure Lemma_Closure_One (G : Graph; X : Vertex_Set)
     with Post => Closure (G, X, 1) = Extend (G, X);

   --  Bounded support: a set whose Nodes are all <= G.Size.  The
   --  closure preserves it (Extend only adds Nodes <= G.Size).

   function Bounded_Support (G : Graph; S : Vertex_Set) return Boolean is
     (for all Node in Vertex => (if S (Node) then Node <= G.Size));

   procedure Lemma_Extend_Support (G : Graph; Reached : Vertex_Set)
     with Pre  => Bounded_Support (G, Reached),
          Post => Bounded_Support (G, Extend (G, Reached));

   procedure Lemma_Closure_Support
     (G : Graph; Reached : Vertex_Set; Fuel : Natural)
     with Pre  => Bounded_Support (G, Reached),
          Post => Bounded_Support (G, Closure (G, Reached, Fuel)),
          Subprogram_Variant => (Decreases => Fuel);

   ---------------------------------------------------------------------------
   --  Cardinality of a set of Nodes and SATURATION of the closure.
   --
   --  The closure is increasing; as long as it is not stable it gains at
   --  least one Node.  Since a set with bounded support has at most G.Size
   --  Nodes, after G.Size steps the closure of a singleton is necessarily stable.
   --  We deduce that extra Fuel changes nothing more.
   ---------------------------------------------------------------------------

   function Cardinal (S : Vertex_Set; From_Idx : Positive) return Natural is
     (if From_Idx > Max_Vertices then 0
      elsif S (From_Idx) then 1 + Cardinal (S, From_Idx + 1)
      else Cardinal (S, From_Idx + 1))
   with Pre  => From_Idx <= Max_Vertices + 1,
        Post => Cardinal'Result <= Max_Vertices - From_Idx + 1,
        Subprogram_Variant => (Increases => From_Idx);

   procedure Lemma_Cardinal_Monotone
     (Petit, Grand : Vertex_Set; From_Idx : Positive)
     with Pre  => From_Idx <= Max_Vertices + 1 and then Included (Petit, Grand),
          Post => Cardinal (Petit, From_Idx) <= Cardinal (Grand, From_Idx),
          Subprogram_Variant => (Increases => From_Idx);

   procedure Lemma_Cardinal_Strict
     (Petit, Grand : Vertex_Set; From_Idx : Positive)
     with Pre  => From_Idx <= Max_Vertices + 1 and then Included (Petit, Grand)
                  and then (for some P in Vertex =>
                              P >= From_Idx and then Petit (P) /= Grand (P)),
          Post => Cardinal (Petit, From_Idx) < Cardinal (Grand, From_Idx),
          Subprogram_Variant => (Increases => From_Idx);

   procedure Lemma_Cardinal_Singleton (U : Vertex)
     with Post => Cardinal (Singleton (U), 1) = 1;

   procedure Lemma_Cardinal_Support (G : Graph; S : Vertex_Set)
     with Pre  => Bounded_Support (G, S),
          Post => Cardinal (S, 1) <= G.Size;

   --  A fixpoint of Extend stays one through any subsequent closure.

   procedure Lemma_Fixpoint_Stable
     (G : Graph; X : Vertex_Set; M : Natural)
     with Pre  => M <= Max_Vertices and then Extend (G, X) = X,
          Post => Closure (G, X, M) = X,
          Subprogram_Variant => (Decreases => M);

   --  A non-stable step strictly increases the cardinality.

   procedure Lemma_Strict_Growth
     (G : Graph; A : Vertex_Set; K : Natural)
     with Pre  => K <= Max_Vertices and then Bounded_Support (G, A)
                  and then Extend (G, Closure (G, A, K)) /= Closure (G, A, K),
          Post => Cardinal (Closure (G, A, K + 1), 1)
                  > Cardinal (Closure (G, A, K), 1);

   --  Accumulation: if the closure is still not stable at step K, it has gained
   --  at least K Nodes from the Start.

   procedure Lemma_Cumul (G : Graph; A : Vertex_Set; K : Natural)
     with Pre  => K <= Max_Vertices and then Bounded_Support (G, A)
                  and then Extend (G, Closure (G, A, K)) /= Closure (G, A, K),
          Post => Cardinal (Closure (G, A, K), 1) >= Cardinal (A, 1) + K,
          Subprogram_Variant => (Decreases => K);

   --  Saturation: at step G.Size the closure of a singleton is stable.

   procedure Lemma_Saturation (G : Graph; U : Vertex)
     with Pre  => In_Graph (G, U),
          Post => Extend (G, Closure (G, Singleton (U), G.Size))
                  = Closure (G, Singleton (U), G.Size);

   --  Consequence: extra Fuel no longer changes the closure.

   procedure Lemma_Closure_Saturated (G : Graph; U : Vertex; M : Natural)
     with Pre  => In_Graph (G, U) and then M <= Max_Vertices,
          Post => Closure (G, Singleton (U), G.Size + M)
                  = Closure (G, Singleton (U), G.Size);

   ---------------------------------------------------------------------------
   --  Connectivity axioms, proven on the model.
   ---------------------------------------------------------------------------

   --  Reflexivity: every Node is Connected to itself.

   procedure Lemma_Reflexive (G : Graph; U : Vertex)
     with Pre  => In_Graph (G, U),
          Post => Reachable (G, U, U);

   --  Transitivity: connectivity composes.

   procedure Lemma_Transitive (G : Graph; U, V, W : Vertex)
     with Pre  => In_Graph (G, U) and then In_Graph (G, V)
                  and then In_Graph (G, W)
                  and then Reachable (G, U, V) and then Reachable (G, V, W),
          Post => Reachable (G, U, W);

   --  Symmetry, pointwise version: if X is reached from U in K steps, then U
   --  is reached from X in K steps (the edges of G being undirected).

   procedure Lemma_Sym_Point (G : Graph; U, X : Vertex; K : Natural)
     with Pre  => K <= Max_Vertices
                  and then In_Graph (G, U) and then In_Graph (G, X)
                  and then Closure (G, Singleton (U), K) (X),
          Post => Closure (G, Singleton (X), K) (U),
          Subprogram_Variant => (Decreases => K);

   --  Symmetry of connectivity.

   procedure Lemma_Symmetric (G : Graph; U, V : Vertex)
     with Pre  => In_Graph (G, U) and then In_Graph (G, V)
                  and then Reachable (G, U, V),
          Post => Reachable (G, V, U);

   ---------------------------------------------------------------------------
   --  Connectivity and graph INCLUSION: adding edges can only
   --  connect more.  (Used for property 2: direction "Res Connected => G
   --  Connected", since Res is a subgraph of G.)
   ---------------------------------------------------------------------------

   --  G1 subgraph of G2: same Nodes, edges of G1 included in G2.

   function Edges_Included (G1, G2 : Graph) return Boolean is
     (G1.Size = G2.Size
      and then
        (for all A in Vertex =>
           (for all B in Vertex =>
              (if A <= G1.Size and then B <= G1.Size
                  and then Has_Edge (G1, A, B)
               then Has_Edge (G2, A, B)))));

   procedure Lemma_Extend_Subgraph
     (G1, G2 : Graph; S : Vertex_Set)
     with Pre  => Edges_Included (G1, G2),
          Post => Included (Extend (G1, S), Extend (G2, S));

   procedure Lemma_Closure_Subgraph
     (G1, G2 : Graph; S : Vertex_Set; Fuel : Natural)
     with Pre  => Edges_Included (G1, G2),
          Post => Included (Closure (G1, S, Fuel), Closure (G2, S, Fuel)),
          Subprogram_Variant => (Decreases => Fuel);

   procedure Lemma_Reachable_Subgraph (G1, G2 : Graph; U, V : Vertex)
     with Pre  => Edges_Included (G1, G2)
                  and then In_Graph (G1, U) and then In_Graph (G1, V)
                  and then Reachable (G1, U, V),
          Post => Reachable (G2, U, V);

   ---------------------------------------------------------------------------
   --  GENERALIZED monotonicity: if every edge of G1 connects Nodes already
   --  Are_Conn in G2 (same Nodes), then every reachability of G1 holds
   --  in G2.  (Used for the hard direction of P2: the edges discarded by Kruskal
   --  connect Nodes already Are_Conn in the Result_G.)
   ---------------------------------------------------------------------------

   function Edges_Connected (G1, G2 : Graph) return Boolean is
     (G1.Size = G2.Size
      and then
        (for all A in Vertex =>
           (for all B in Vertex =>
              (if A <= G1.Size and then B <= G1.Size
                  and then Has_Edge (G1, A, B)
               then Reachable (G2, A, B)))));

   procedure Lemma_Closure_Via_Edges
     (G1, G2 : Graph; U, Target : Vertex; Fuel : Natural)
     with Pre  => Fuel <= Max_Vertices
                  and then Edges_Connected (G1, G2)
                  and then In_Graph (G1, U)
                  and then Closure (G1, Singleton (U), Fuel) (Target),
          Post => Reachable (G2, U, Target),
          Subprogram_Variant => (Decreases => Fuel);

   procedure Lemma_Reachable_Via_Edges (G1, G2 : Graph; U, V : Vertex)
     with Pre  => Edges_Connected (G1, G2)
                  and then In_Graph (G1, U) and then In_Graph (G1, V)
                  and then Reachable (G1, U, V),
          Post => Reachable (G2, U, V);

   --  Quantified version of subgraph monotonicity: every Connection of G1 is
   --  a Connection of G2 (useful to propagate connectivity when adding
   --  an edge: the Old_Arr graph is a subgraph of the New_Arr).
   procedure Lemma_Reachable_Subgraph_All (G1, G2 : Graph)
     with Pre  => Edges_Included (G1, G2),
          Post =>
            (for all U in Vertex =>
               (for all V in Vertex =>
                  (if In_Graph (G1, U) and then In_Graph (G1, V)
                      and then Reachable (G1, U, V)
                   then Reachable (G2, U, V))));

   ---------------------------------------------------------------------------
   --  DECOMPOSITION WHEN ADDING AN EDGE (key to acyclicity, P3).
   --
   --  If G2 is G1 with the edge {X, Y} added (same Nodes, equal
   --  elsewhere), then every reachability of G2 reduces to G1: either A reaches
   --  B without the edge (in G1), or the Path goes through {X, Y} (A~X and Y~B, or
   --  A~Y and X~B, in G1).  Proven by induction on the closure of G2,
   --  reusing reflexivity / edge / symmetry / transitivity of G1.
   ---------------------------------------------------------------------------

   --  Extraction of an edge equality from Same_Except (instantiation in a
   --  minimal context so as not to blow up the prover).
   procedure Lemma_Same_Except_Edge
     (G1, G2 : Graph; U, V, A, B : Vertex)
     with Ghost,
       Pre  => G1.Size = G2.Size and then Same_Except (G1, G2, U, V)
               and then In_Graph (G1, A) and then In_Graph (G1, B)
               and then (A /= U or else B /= V)
               and then (A /= V or else B /= U),
       Post => Has_Edge (G1, A, B) = Has_Edge (G2, A, B)
               and then (if Has_Edge (G1, A, B)
                         then Edge_Length (G1, A, B) = Edge_Length (G2, A, B));

   --  Same_Except is transitive (same edge {U,V} excluded).
   procedure Lemma_SE_Trans (G1, G2, G3 : Graph; U, V : Vertex)
     with Ghost,
       Pre  => G1.Size = G2.Size and then G2.Size = G3.Size
               and then Same_Except (G1, G2, U, V)
               and then Same_Except (G2, G3, U, V),
       Post => Same_Except (G1, G3, U, V);

   --  If G1 and G2 agree except on {U,V} and G1 does not have the edge {U,V},
   --  then the edges of G1 are included in G2.
   procedure Lemma_SE_Included (G1, G2 : Graph; U, V : Vertex)
     with Ghost,
       Pre  => G1.Size = G2.Size
               and then In_Graph (G1, U) and then In_Graph (G1, V)
               and then Same_Except (G1, G2, U, V)
               and then not Has_Edge (G1, U, V),
       Post => Edges_Included (G1, G2);

   procedure Lemma_Closure_Add
     (G1, G2 : Graph; X, Y, A, Target : Vertex; Fuel : Natural)
     with Pre  => Fuel <= Max_Vertices
                  and then G1.Size = G2.Size
                  and then In_Graph (G1, X) and then In_Graph (G1, Y)
                  and then In_Graph (G1, A)
                  and then Same_Except (G2, G1, X, Y)
                  and then Has_Edge (G2, X, Y)
                  and then Closure (G2, Singleton (A), Fuel) (Target),
          Post => Reachable (G1, A, Target)
                  or else (Reachable (G1, A, X)
                           and then Reachable (G1, Y, Target))
                  or else (Reachable (G1, A, Y)
                           and then Reachable (G1, X, Target)),
          Subprogram_Variant => (Decreases => Fuel);

   procedure Lemma_Reachable_Add (G1, G2 : Graph; X, Y, A, B : Vertex)
     with Pre  => G1.Size = G2.Size
                  and then In_Graph (G1, X) and then In_Graph (G1, Y)
                  and then In_Graph (G1, A) and then In_Graph (G1, B)
                  and then Same_Except (G2, G1, X, Y)
                  and then Has_Edge (G2, X, Y)
                  and then Reachable (G2, A, B),
          Post => Reachable (G1, A, B)
                  or else (Reachable (G1, A, X) and then Reachable (G1, Y, B))
                  or else (Reachable (G1, A, Y)
                           and then Reachable (G1, X, B));

   --  An edge Connects its endpoints.

   procedure Lemma_Edge (G : Graph; U, V : Vertex)
     with Pre  => In_Graph (G, U) and then In_Graph (G, V)
                  and then Has_Edge (G, U, V),
          Post => Reachable (G, U, V);

   ---------------------------------------------------------------------------
   --  NUMBER OF CONNECTED COMPONENTS
   --
   --  We count the REPRESENTATIVES: a Node V is the representative of its
   --  component if no smaller Node is Reachable to it.  The number
   --  of components is the number of representatives.
   ---------------------------------------------------------------------------

   --  OPAQUE (defining post): the quantified term "not Reachable" is
   --  thus hidden behind an abstract boolean, which prevents it from
   --  re-expanding in the loop invariants (component counting).
   function Is_Representative (G : Graph; V : Vertex) return Boolean
   with Ghost, Pre => In_Graph (G, V),
        Post => Is_Representative'Result =
                  (for all U in Vertex => (if U < V then not Reachable (G, U, V)));

   --  REPRESENTATIVE of a Node = smallest Node of its component.  Search
   --  for the first W (>= the parameter) Reachable to V; V itself works
   --  (reflexivity), so the search stops at the latest at W = V.
   function Rep_Search (G : Graph; V : Vertex; W : Vertex) return Vertex
   with Ghost,
        Pre  => V <= G.Size and then W <= V,
        Post => Rep_Search'Result <= V
                and then Reachable (G, Rep_Search'Result, V)
                and then (for all X in Vertex =>
                            (if W <= X and then X < Rep_Search'Result
                             then not Reachable (G, X, V))),
        Subprogram_Variant => (Decreases => V - W);

   function Rep (G : Graph; V : Vertex) return Vertex is (Rep_Search (G, V, 1))
   with Ghost, Pre => In_Graph (G, V),
        Post => Rep'Result <= V and then Reachable (G, Rep'Result, V)
                and then (for all X in Vertex =>
                            (if X < Rep'Result then not Reachable (G, X, V)));

   --  Is_Representative (V) <=> Rep (V) = V.
   procedure Lemma_Rep_Is_Rep (G : Graph; V : Vertex) with Ghost,
     Pre  => In_Graph (G, V),
     Post => (Is_Representative (G, V) = (Rep (G, V) = V));

   --  Two Nodes of the same component have the same representative.
   procedure Lemma_Rep_Same_Comp (G : Graph; U, V : Vertex) with Ghost,
     Pre  => In_Graph (G, U) and then In_Graph (G, V)
             and then Reachable (G, U, V),
     Post => Rep (G, U) = Rep (G, V);

   function Nb_Comp_From (G : Graph; From_Idx : Positive) return Natural is
     (if From_Idx > G.Size then 0
      elsif Is_Representative (G, From_Idx) then 1 + Nb_Comp_From (G, From_Idx + 1)
      else Nb_Comp_From (G, From_Idx + 1))
   with Ghost,
        Pre  => From_Idx <= Max_Vertices + 1,
        Post => Nb_Comp_From'Result <= Max_Vertices + 1 - From_Idx,
        Subprogram_Variant => (Increases => From_Idx);

   function Nb_Components (G : Graph) return Natural is (Nb_Comp_From (G, 1))
   with Ghost;

   --  TRANSFER: in a SUBGRAPH, a representative stays one (fewer edges
   --  => less reachability => no smaller one reaches it either).
   procedure Lemma_Rep_Transfer (H, G : Graph; W : Vertex)
     with Ghost,
       Pre  => Edges_Included (H, G) and then In_Graph (G, W),
       Post => (if Is_Representative (G, W) then Is_Representative (H, W));

   --  COUNT +1: if the representatives of K and F coincide EVERYWHERE except at a
   --  single Node M (representative in K, not in F), then K has exactly one
   --  more component.  (The hard content -- identifying M and proving the agreement
   --  elsewhere -- is provided by the caller; here, pure counting by induction.)
   procedure Lemma_Comp_Plus_One
     (K, F : Graph; M : Vertex; From_Idx : Positive)
     with Ghost,
       Pre  => K.Size = F.Size and then M <= K.Size
               and then From_Idx <= Max_Vertices + 1
               and then (for all W in Vertex =>
                           (if W <= K.Size and then W /= M
                            then Is_Representative (K, W) = Is_Representative (F, W)))
               and then Is_Representative (K, M)
               and then not Is_Representative (F, M),
       Post => Nb_Comp_From (K, From_Idx)
               = Nb_Comp_From (F, From_Idx) + (if From_Idx <= M then 1 else 0),
       Subprogram_Variant => (Increases => From_Idx);

   --  MONOTONICITY (fact M): a SUBGRAPH has AT LEAST as many components
   --  (fewer edges => fewer connections => more components).
   procedure Lemma_Nb_Comp_Monotone (H, G : Graph; From_Idx : Positive)
     with Ghost,
       Pre  => Edges_Included (H, G) and then From_Idx <= Max_Vertices + 1,
       Post => Nb_Comp_From (H, From_Idx) >= Nb_Comp_From (G, From_Idx),
       Subprogram_Variant => (Increases => From_Idx);

   --  MONOTONICITY BY REACHABILITY: if B is MORE connected than A (every
   --  Connection of A holds in B), then B has AT MOST as many components.
   --  (Like Lemma_Nb_Comp_Monotone but based on reachability rather than
   --  on edge inclusion -- necessary for the greedy property.)
   procedure Lemma_Nb_Comp_Reach (A, B : Graph; From_Idx : Positive)
     with Ghost,
       Pre  => A.Size = B.Size and then From_Idx <= Max_Vertices + 1
               and then (for all U in Vertex =>
                           (for all V in Vertex =>
                              (if In_Graph (A, U) and then In_Graph (A, V)
                                  and then Reachable (A, U, V)
                               then Reachable (B, U, V)))),
       Post => Nb_Comp_From (B, From_Idx) <= Nb_Comp_From (A, From_Idx),
       Subprogram_Variant => (Increases => From_Idx);

   --  EQUIVALENCE: if A and B have the SAME reachability for every pair, they have
   --  the same number of components (double application of Lemma_Nb_Comp_Reach).
   procedure Lemma_Nb_Comp_Equiv (A, B : Graph)
     with Ghost,
       Pre  => A.Size = B.Size
               and then (for all U in Vertex =>
                           (for all V in Vertex =>
                              (if In_Graph (A, U) and then In_Graph (A, V)
                               then Reachable (A, U, V)
                                    = Reachable (B, U, V)))),
       Post => Nb_Components (A) = Nb_Components (B);

   --  CONGRUENCE: if the representatives of K and F coincide EVERYWHERE, the two
   --  graphs have the same number of components.  (Used for the case "removal of a
   --  non-bridge edge", where no component splits.)
   procedure Lemma_Nb_Comp_Cong (K, F : Graph; From_Idx : Positive)
     with Ghost,
       Pre  => K.Size = F.Size and then From_Idx <= Max_Vertices + 1
               and then (for all W in Vertex =>
                           (if W <= K.Size
                            then Is_Representative (K, W)
                                 = Is_Representative (F, W))),
       Post => Nb_Comp_From (K, From_Idx) = Nb_Comp_From (F, From_Idx),
       Subprogram_Variant => (Increases => From_Idx);

   ---------------------------------------------------------------------------
   --  CLOSURE AVOIDING A FORBIDDEN SET
   --
   --  Same construction as Extend / Closure, but a forbidden Node is NEVER
   --  added.  This tool serves to prove the COMPLETENESS of the depth-first
   --  traversal (the Findable model of kruskal) with respect to
   --  reachability: Findable avoids the already visited Nodes exactly
   --  as this closure avoids the Forbidden Nodes.
   ---------------------------------------------------------------------------

   --  Mark a Node in a set (pointwise update).

   function Mark (S : Vertex_Set; Node : Vertex)
     return Vertex_Set
   is
     (for K in Vertex => (if K = Node then True else S (K)));

   --  A closure step that does not enter the Forbidden Nodes.  OPAQUE
   --  (normal function, not an expression) for the same reasons as Extend.

   function Avoiding_Extend
     (G : Graph; Reached, Forbidden : Vertex_Set)
     return Vertex_Set
     with Post =>
       (for all Node in Vertex =>
          Avoiding_Extend'Result (Node) =
            (Reached (Node)
             or else (Node <= G.Size
                      and then not Forbidden (Node)
                      and then (for some Neighbour in Vertex =>
                                  Neighbour <= G.Size
                                  and then Reached (Neighbour)
                                  and then Has_Edge (G, Neighbour, Node)))));

   --  Expression function (like Closure): the definition axiom makes the
   --  recursive lemmas (composition, growth, ...) stable.  The congruences
   --  f (x) = f (y) that used to diverge are now handled by the dedicated lemma
   --  Lemma_AC_Congruence (explicit induction), not by the raw prover.

   function Avoiding_Closure
     (G : Graph; Reached, Forbidden : Vertex_Set; Fuel : Natural)
     return Vertex_Set
   is
     (if Fuel = 0 then Reached
      else Avoiding_Closure
             (G, Avoiding_Extend (G, Reached, Forbidden), Forbidden,
              Fuel - 1))
   with Subprogram_Variant => (Decreases => Fuel);

   --  Basic lemmas, analogous to those of Closure.

   procedure Lemma_AE_Increasing
     (G : Graph; Reached, Forbidden : Vertex_Set)
     with Post => Included (Reached, Avoiding_Extend (G, Reached, Forbidden));

   procedure Lemma_AC_Increasing
     (G : Graph; Reached, Forbidden : Vertex_Set; Fuel : Natural)
     with Post => Included (Reached,
                          Avoiding_Closure (G, Reached, Forbidden, Fuel)),
          Subprogram_Variant => (Decreases => Fuel);

   procedure Lemma_AC_Composition
     (G : Graph; Reached, Forbidden : Vertex_Set; N, M : Natural)
     with Pre  => N <= Max_Vertices and then M <= Max_Vertices,
          Post => Avoiding_Closure (G, Reached, Forbidden, N + M)
                  = Avoiding_Closure
                      (G, Avoiding_Closure (G, Reached, Forbidden, N),
                       Forbidden, M),
          Subprogram_Variant => (Decreases => N);

   procedure Lemma_AC_One
     (G : Graph; Reached, Forbidden : Vertex_Set)
     with Post => Avoiding_Closure (G, Reached, Forbidden, 1)
                  = Avoiding_Extend (G, Reached, Forbidden);

   procedure Lemma_AC_Fuel_Increasing
     (G : Graph; Reached, Forbidden : Vertex_Set; Fuel : Natural)
     with Pre  => Fuel <= Max_Vertices,
          Post => Included (Avoiding_Closure (G, Reached, Forbidden, Fuel),
                          Avoiding_Closure (G, Reached, Forbidden,
                                           Fuel + 1));

   --  Congruence: two EQUAL Forbidden sets give the same avoiding
   --  closure (at the point Target).  ISOLATED lemma: the congruence f (x) = f (y) on
   --  the opaque function Avoiding_Closure is trivial in a small context,
   --  whereas in Row (large context) it exhausted the prover.

   procedure Lemma_AC_Congruence
     (G : Graph;
      Atteints1, Atteints2, Interdits1, Interdits2 : Vertex_Set;
      Fuel : Natural; Target : Vertex)
     with Pre  => Atteints1 = Atteints2 and then Interdits1 = Interdits2
                  and then Avoiding_Closure
                             (G, Atteints1, Interdits1, Fuel) (Target),
          Post => Avoiding_Closure
                    (G, Atteints2, Interdits2, Fuel) (Target),
          Subprogram_Variant => (Decreases => Fuel);

   --  Without any forbidden node, the avoiding closure coincides with the closure.

   --  Without a forbidden node, an avoiding step = an ordinary step.

   procedure Lemma_AE_Empty
     (G : Graph; Reached, Forbidden : Vertex_Set)
     with Pre  => (for all K in Vertex => not Forbidden (K)),
          Post => Avoiding_Extend (G, Reached, Forbidden)
                  = Extend (G, Reached);

   procedure Lemma_AC_Empty
     (G : Graph; Reached, Forbidden : Vertex_Set; Fuel : Natural)
     with Pre  => Fuel <= Max_Vertices
                  and then (for all K in Vertex => not Forbidden (K)),
          Post => Avoiding_Closure (G, Reached, Forbidden, Fuel)
                  = Closure (G, Reached, Fuel),
          Subprogram_Variant => (Decreases => Fuel);

   --  FIRST STEP (core of completeness): if Target (distinct from Start) is
   --  reached from Start avoiding Forbidden, then there exists a Neighbour of
   --  Start, not forbidden, from which Target is reached while also avoiding
   --  Start.  Proven by induction on the Fuel, peeling the FIRST step
   --  (the edge out of Start): the immediate predecessor of Target is reached
   --  from that same Neighbour.  The Neighbour is returned by an out parameter
   --  (avoids extracting an existential Witness).

   procedure Lemma_First_Step
     (G         : Graph;
      Start    : Vertex;
      Target     : Vertex;
      Forbidden : Vertex_Set;
      Fuel : Natural;
      Neighbour    : out Vertex)
     with
       Pre  => Start <= G.Size and then Target <= G.Size
               and then Fuel <= Max_Vertices
               and then not Forbidden (Start)
               and then Start /= Target
               and then Avoiding_Closure
                          (G, Singleton (Start), Forbidden, Fuel) (Target),
       Post => Neighbour <= G.Size
               and then Has_Edge (G, Start, Neighbour)
               and then not Forbidden (Neighbour)
               and then Avoiding_Closure
                          (G, Singleton (Neighbour), Mark (Forbidden, Start),
                           Fuel) (Target),
       Subprogram_Variant => (Decreases => Fuel);

end Connectivity;
