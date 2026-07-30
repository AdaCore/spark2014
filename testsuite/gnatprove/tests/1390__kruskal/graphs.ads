------------------------------------------------------------------------------
--  Graphs
--
--  An *undirected*, *weighted* graph, represented as an adjacency matrix.
--
--  A graph holds up to Max_Vertices (1000) vertices.  Each graph value carries
--  its actual number of vertices as a discriminant, Size, so graphs of any size
--  from 0 to 1000 can coexist; the adjacency matrix is stored exactly
--  Size x Size (no fixed 1000 x 1000 cost per graph).  Vertices of a graph G
--  are the values 1 .. G.Size; the predicate In_Graph (G, V) says so.
--
--  "Undirected" is guaranteed *by construction*: an edge between U and V is
--  stored once, at the canonical cell (min (U, V), max (U, V)).  Every query
--  reads that same canonical cell, so Has_Edge (G, U, V) and Has_Edge (G, V, U)
--  denote literally the same matrix element -- symmetry is definitional, not an
--  invariant that has to be maintained.  See the Symmetry lemma below.
--
--  "No self-loops" *is* a maintained invariant (a type predicate): the diagonal
--  of the matrix is always empty.
--
--  "Weighted / with distances": every edge carries a Weight, returned by
--  Edge_Length (G, U, V) -- the distance between two adjacent vertices.
------------------------------------------------------------------------------

package Graphs
  with SPARK_Mode => On
is

   Max_Vertices : constant := 1000;
   --  Largest graph this package supports.

   subtype Vertex is Positive range 1 .. Max_Vertices;
   --  A potential vertex name / matrix index.

   subtype Vertex_Count is Natural range 0 .. Max_Vertices;
   --  A number of vertices (0 for the empty graph).

   Max_Weight : constant := 1_000_000;
   --  Largest edge length supported.  Bounding the weight keeps threshold and
   --  weight-sum reasoning within Integer (needed for the minimality proof).

   subtype Weight is Positive range 1 .. Max_Weight;
   --  The distance (length) carried by an edge.  Strictly positive: a present
   --  edge always has a meaningful, non-zero distance.

   subtype Weight_Threshold is Natural range 0 .. Max_Weight;
   --  A weight THRESHOLD.  Includes 0 (keeps no edge, all lengths being >= 1),
   --  unlike Weight; used to threshold a graph (Restrict) for the minimality
   --  proof.

   subtype Degree_Count is Vertex_Count;
   --  Number of neighbours of a vertex (at most Size - 1, bounded here by the
   --  wider Vertex_Count).

   type Graph (Size : Vertex_Count) is private;
   --  An undirected weighted graph on the vertices 1 .. Size.  Symmetric by
   --  construction; the diagonal (self-loops) is always empty.

   function In_Graph (G : Graph; V : Vertex) return Boolean is (V <= G.Size);
   --  True when V is one of G's vertices, i.e. V in 1 .. G.Size.

   ---------------------------------------------------------------------------
   --  Queries
   ---------------------------------------------------------------------------

   function Has_Edge (G : Graph; U, V : Vertex) return Boolean
     with Pre => In_Graph (G, U) and then In_Graph (G, V);
   --  True when an edge connects U and V.  Symmetric: see Symmetry.

   function Edge_Length (G : Graph; U, V : Vertex) return Weight
     with Pre =>
       In_Graph (G, U) and then In_Graph (G, V) and then Has_Edge (G, U, V);
   --  The distance carried by the edge between U and V.

   ---------------------------------------------------------------------------
   --  Undirectedness, as a (trivially provable) lemma
   ---------------------------------------------------------------------------

   procedure Symmetry (G : Graph; U, V : Vertex)
     with
       Ghost,
       Pre  => In_Graph (G, U) and then In_Graph (G, V),
       Post =>
         Has_Edge (G, U, V) = Has_Edge (G, V, U)
         and then
           (if Has_Edge (G, U, V) then
              Edge_Length (G, U, V) = Edge_Length (G, V, U));
   --  A ghost lemma making the (definitional) symmetry of the graph available
   --  to clients as a usable fact: edges and distances do not depend on the
   --  order of their endpoints.

   procedure No_Self_Loop (G : Graph; V : Vertex)
     with Ghost,
       Pre  => In_Graph (G, V),
       Post => not Has_Edge (G, V, V);
   --  A ghost lemma exposing the (private) Loop_Free type predicate to clients:
   --  a graph never has an edge from a vertex to itself.

   ---------------------------------------------------------------------------
   --  "Unchanged elsewhere" frame property
   --
   --  Same_Except (G1, G2, U, V) holds when two graphs of the same size agree
   --  on the presence and length of *every* edge other than the unordered pair
   --  {U, V}.  It is the frame condition used by the mutating operations below.
   ---------------------------------------------------------------------------

   function Same_Except (G1, G2 : Graph; U, V : Vertex) return Boolean is
     (for all A in Vertex =>
        (for all B in Vertex =>
           (if In_Graph (G1, A) and then In_Graph (G1, B)
               and then (A /= U or else B /= V)
               and then (A /= V or else B /= U)
            then
              Has_Edge (G1, A, B) = Has_Edge (G2, A, B)
              and then
                (if Has_Edge (G1, A, B) then
                   Edge_Length (G1, A, B) = Edge_Length (G2, A, B)))))
   with Ghost, Pre => G1.Size = G2.Size;

   ---------------------------------------------------------------------------
   --  Constructors / mutators
   ---------------------------------------------------------------------------

   function Empty_Graph (Size : Vertex_Count) return Graph
     with Post =>
       Empty_Graph'Result.Size = Size
       and then
         (for all U in Vertex =>
            (for all V in Vertex =>
               (if U <= Size and then V <= Size then
                  not Has_Edge (Empty_Graph'Result, U, V))));
   --  A graph on Size vertices with no edges.

   procedure Add_Edge (G : in out Graph; U, V : Vertex; Length : Weight)
     with
       Pre  => In_Graph (G, U) and then In_Graph (G, V) and then U /= V,
       Post =>
         G.Size = G'Old.Size
         and then Has_Edge (G, U, V)
         and then Has_Edge (G, V, U)
         and then Edge_Length (G, U, V) = Length
         and then Edge_Length (G, V, U) = Length
         and then Same_Except (G, G'Old, U, V);
   --  Connect U and V with an edge of the given Length (or update the length
   --  of an existing edge).  Self-loops are excluded by the precondition.

   procedure Remove_Edge (G : in out Graph; U, V : Vertex)
     with
       Pre  => In_Graph (G, U) and then In_Graph (G, V),
       Post =>
         G.Size = G'Old.Size
         and then not Has_Edge (G, U, V)
         and then not Has_Edge (G, V, U)
         and then Same_Except (G, G'Old, U, V);
   --  Remove the edge between U and V (a no-op when there is no such edge).

   --  The THRESHOLDED graph: G keeping only the edges of length <= Threshold.
   --  Used (ghost) to reason by weight thresholds (minimality / P4).
   function Restrict (G : Graph; Threshold : Weight_Threshold) return Graph
     with Ghost,
       Post =>
         Restrict'Result.Size = G.Size
         and then
           (for all A in Vertex =>
              (for all B in Vertex =>
                 (if In_Graph (G, A) and then In_Graph (G, B) then
                    Has_Edge (Restrict'Result, A, B) =
                      (Has_Edge (G, A, B)
                       and then Edge_Length (G, A, B) <= Threshold))))
         and then
           (for all A in Vertex =>
              (for all B in Vertex =>
                 (if In_Graph (G, A) and then In_Graph (G, B)
                     and then Has_Edge (Restrict'Result, A, B)
                  then Edge_Length (Restrict'Result, A, B)
                       = Edge_Length (G, A, B))));

   ---------------------------------------------------------------------------
   --  Derived information
   ---------------------------------------------------------------------------

   function Degree (G : Graph; Source : Vertex) return Degree_Count
     with
       Pre  => In_Graph (G, Source),
       Post =>
         (Degree'Result = 0) =
           (for all V in Vertex =>
              (if In_Graph (G, V) then not Has_Edge (G, Source, V)));
   --  Number of vertices adjacent to Source.

private

   type Edge is record
      Present : Boolean := False;
      --  Whether the edge exists.
      Length  : Weight  := 1;
      --  The distance carried by the edge; meaningful only when Present.
   end record;

   No_Edge : constant Edge := (Present => False, Length => 1);

   type Matrix is array (Positive range <>, Positive range <>) of Edge;

   --  Canonical orientation of an unordered pair: edges live in the upper
   --  triangle (row <= column).  Lo/Hi are symmetric in their arguments, which
   --  is exactly what makes graph symmetry definitional.

   function Lo (U, V : Vertex) return Vertex is (if U <= V then U else V);
   function Hi (U, V : Vertex) return Vertex is (if U <= V then V else U);

   function Loop_Free (M : Matrix) return Boolean is
     (for all V in M'Range (1) =>
        (if V in M'Range (2) then not M (V, V).Present))
   with Ghost;

   type Graph (Size : Vertex_Count) is record
      Adj : Matrix (1 .. Size, 1 .. Size);
   end record
     with Ghost_Predicate => Loop_Free (Adj);

   --  Completions of the public query functions: both read the *canonical*
   --  cell, so they are insensitive to the order of U and V.

   function Has_Edge (G : Graph; U, V : Vertex) return Boolean is
     (G.Adj (Lo (U, V), Hi (U, V)).Present);

   function Edge_Length (G : Graph; U, V : Vertex) return Weight is
     (G.Adj (Lo (U, V), Hi (U, V)).Length);

end Graphs;
