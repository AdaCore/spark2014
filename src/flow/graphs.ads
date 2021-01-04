------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                               G R A P H S                                --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2013-2021, Altran UK Limited                --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers;
with Ada.Containers.Vectors;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Hashed_Sets;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;

--  A graph library. Although reasonably generic, it was implemented
--  for the SPARK 2014 flow analysis which dictated its design. In
--  particular the curious limitation that vertices may not be removed
--  once added to the graph is perfectly OK for flow analysis.
--
--  Each vertex is identified by a Vertex_Id which is valid for the
--  entire lifetime of a graph. Furthermore if a graph A is based on
--  another graph B, then any Vertex_Id valid in one is valid in the
--  other, and they refer to the same vertex, provided no new vertices
--  have been added to A or B.
--
--  Vertices and edges may have properties and they are copied when
--  one graph is created from another; however they are distinct from
--  that point on.
--
--  The graph itself is implemented as a double adjacency list using
--  hashed sets and maps: each vertex has a set of in-neighbours and a
--  map of out neighbours to edge properties. Note that the list of
--  in-neighbours is not strictly necessary, it is merely an
--  optimisation to make lookup of in-neighbours faster (linear to
--  near constant) as a number of algorithms require or construct
--  this, in particular the dominance frontier and related algorithms.
--
--  A few notes on complexity, where not optimal:
--
--     * Graph reversal could be implemented in a better (constant
--       time) way, but we only reverse each flow graph once and each
--       PDG once. Furthermore, due to the nature of these graphs we
--       can expect runtime to be nearer to linear time instead of
--       quadratic.
--
--     * Transitive closure could improved by implementing the STACK_TC
--       algorithm, but as it requires a topological sort it is significantly
--       more difficult to implement. Deferred until we actully feel like this
--       is a performance problem.
--
--  A few other implementation notes:
--
--     * The iterator scheme is fairly complex and we use the GNAT iterable
--       extension.
--
--     * For each concept in graph theory there seem to be at least
--       two words commonly used in the literature. I have used the
--       following:
--
--          Vertex        (rather than Node)
--          Edge          (rather than Link)
--          In_Neighbour  (rather than Predecessor)
--          Out_Neighbour (rather than Successor)

generic
   type Vertex_Key is private;
   type Edge_Colours is (<>);
   Null_Key : Vertex_Key;
   with function Key_Hash (Element : Vertex_Key)
                           return Ada.Containers.Hash_Type;
   with function Test_Key (A, B : Vertex_Key) return Boolean;
package Graphs is
   type Graph is tagged private;

   type Vertex_Id is private;
   Null_Vertex : constant Vertex_Id;

   type Cluster_Id is private;
   Null_Cluster : constant Cluster_Id;

   type Collection_Type_T is
     (
      --  Collections based on a vertex.
      Out_Neighbours,
      In_Neighbours,

      --  Collections over the graph.
      All_Vertices);

   subtype Vertex_Based_Collection is Collection_Type_T
     range Out_Neighbours .. In_Neighbours;

   subtype Graph_Based_Collection is Collection_Type_T
     range All_Vertices .. All_Vertices;

   type Vertex_Collection_T (The_Type : Collection_Type_T) is private with
     Iterable => (First       => First_Cursor,
                  Next        => Next_Cursor,
                  Has_Element => Has_Element,
                  Element     => Get_Element);

   type Cursor (Collection_Type : Collection_Type_T) is private;

   type Traversal_Instruction is (Continue,
                                  Skip_Children,
                                  Abort_Traversal,
                                  Found_Destination);

   subtype Simple_Traversal_Instruction is Traversal_Instruction
     range Continue .. Abort_Traversal;

   type Strongly_Connected_Components is private;

   ----------------------------------------------------------------------
   --  Basic operations
   ----------------------------------------------------------------------

   function Is_Frozen (G : Graph) return Boolean;
   --  Returns true if the graph is frozen, i.e. vertices may not be added.
   --  Edges may still be added or removed however.

   function Create (Colour : Edge_Colours := Edge_Colours'First) return Graph;
   --  Creates a new, empty graph.

   function Create (G             : Graph;
                    Copy_Clusters : Boolean := False)
                    return Graph
   with Post => Create'Result.Is_Frozen;
   --  Creates a new graph with all the vertices from G, but no edges. Both
   --  graphs are frozen by this operation.

   ----------------------------------------------------------------------
   --  Vertex operations
   ----------------------------------------------------------------------

   --  Please note there is no Remove_Vertex, this is not an accident as it is
   --  not needed. Also, it would not be possible to implement.
   --
   --  As a consequence all vertex ids are valid for the lifetime of
   --  the graph object.

   function Contains
     (G : Graph;
      V : Vertex_Key)
      return Boolean;
   --  Returns True iff the graph contains a vertex with key V.
   --
   --  Complexity is O(1)

   function Get_Vertex
     (G : Graph;
      V : Vertex_Key)
      return Vertex_Id;
   --  Search the vertex group for the given vertex and return its
   --  Id. If not found, Null_Vertex is returned.
   --
   --  Complexity is O(1) (in the general case).

   function Get_Key
     (G : Graph;
      V : Vertex_Id)
      return Vertex_Key
   with Pre => V /= Null_Vertex;
   --  Obtain the key for the given vertex.
   --
   --  Complexity is O(1).

   procedure Add_Vertex
     (G  : in out Graph;
      V  : Vertex_Key;
      Id : out Vertex_Id)
   with Pre  => not G.Is_Frozen and then not G.Contains (V),
        Post => Id /= Null_Vertex;
   --  Add a new vertex to the graph, with no edges attached.
   --
   --  Complexity is O(1) in the general case, but presumably can be
   --  O(N) if the internal vector is resized.

   procedure Add_Vertex
     (G  : in out Graph;
      Id : out Vertex_Id)
   with Pre  => not G.Is_Frozen,
        Post => Id /= Null_Vertex;
   --  Adds an unkeyed vertex. You must never lose the returned Id,
   --  otherwise you lose the vertex!

   procedure Add_Vertex
     (G : in out Graph;
      V : Vertex_Key)
   with Pre => not G.Is_Frozen and then not G.Contains (V);
   --  Add a new keyed vertex, but do not return its Id.

   procedure Include_Vertex
     (G : in out Graph;
      V : Vertex_Key)
   with Pre => not G.Is_Frozen;
   --  Add a new keyed vertex if it does not already exists; otherwise do
   --  nothing.

   function Vertex_Hash
     (Element : Vertex_Id) return Ada.Containers.Hash_Type;
   --  Hash a vertex_id (useful for building sets of vertices).

   function Num_Vertices (G : Graph) return Natural;
   --  @param G a graph
   --  @return the number of vertices of G

   ----------------------------------------------------------------------
   --  Edge operations
   ----------------------------------------------------------------------

   function In_Neighbour_Count
     (G : Graph;
      V : Vertex_Id) return Natural
   with Pre => V /= Null_Vertex;
   --  Returns the number of in neighbours for the given vertex.
   --
   --  Complexity is O(1).

   function Out_Neighbour_Count
     (G : Graph;
      V : Vertex_Id) return Natural
   with Pre => V /= Null_Vertex;
   --  Returns the number of out neighbours for the given vertex.
   --
   --  Complexity is O(1).

   function Edge_Exists
     (G        : Graph;
      V_1, V_2 : Vertex_Id) return Boolean
   with Pre => V_1 /= Null_Vertex and then V_2 /= Null_Vertex;
   --  Tests if the given edge from V_1 to V_2 is in the graph.
   --
   --  Complexity is O(1).

   function Edge_Exists
     (G        : Graph;
      V_1, V_2 : Vertex_Key) return Boolean
   with Pre => G.Contains (V_1) and then G.Contains (V_2);
   --  Same as above but takes Vertex_Keys as parameters.

   function Edge_Exists
     (G        : Graph;
      SCC      : Strongly_Connected_Components;
      V_1, V_2 : Vertex_Id) return Boolean
   with Pre => V_1 /= Null_Vertex and then V_2 /= Null_Vertex;
   --  Same as above but using a precomputed graph of strongly connected
   --  components.

   function Edge_Exists
     (G        : Graph;
      SCC      : Strongly_Connected_Components;
      V_1, V_2 : Vertex_Key) return Boolean
   with Pre => G.Contains (V_1) and then G.Contains (V_2);
   --  Same as above but using a precomputed graph of strongly connected
   --  components.

   function Edge_Colour
     (G        : Graph;
      V_1, V_2 : Vertex_Id) return Edge_Colours
   with Pre => G.Edge_Exists (V_1, V_2);
   --  Returns the edge colour of the given edge.

   procedure Add_Edge
     (G        : in out Graph;
      V_1, V_2 : Vertex_Id;
      Colour   : Edge_Colours := Edge_Colours'First)
   with Pre  => V_1 /= Null_Vertex and then V_2 /= Null_Vertex,
        Post => G.Edge_Exists (V_1, V_2);
   --  Adds an unmarked edge from V_1 to V_2. If the edge already
   --  exists, we do nothing (i.e. existing edge attributes do not
   --  change).
   --
   --  Complexity is O(1).

   procedure Add_Edge
     (G        : in out Graph;
      V_1, V_2 : Vertex_Key;
      Colour   : Edge_Colours := Edge_Colours'First)
   with Pre => G.Contains (V_1) and then G.Contains (V_2);
   --  Convenience function to add an edge between two vertices given
   --  by key (instead of id).
   --
   --  Complexity is O(1) (in general due to use of Get_Vertex).

   procedure Remove_Edge
     (G        : in out Graph;
      V_1, V_2 : Vertex_Id)
   with Pre  => V_1 /= Null_Vertex and then V_2 /= Null_Vertex,
        Post => not G.Edge_Exists (V_1, V_2);
   --  Removes the edge from V_1 to V_2 from the graph, if it exists.
   --
   --  Complexity is O(1).

   procedure Mark_Edge
     (G        : in out Graph;
      V_1, V_2 : Vertex_Id)
   with Pre  => G.Edge_Exists (V_1, V_2),
        Post => G.Edge_Exists (V_1, V_2);
   --  Mark the edge from V_1 to V_2 in the graph.
   --
   --  Complexity is O(1).

   procedure Clear_Vertex
     (G : in out Graph;
      V : Vertex_Id)
   with Pre => V /= Null_Vertex;
   --  Remove all in and out edges from the given vertex.
   --
   --  Complexity is O(N).

   procedure Copy_Edges
     (G : in out Graph;
      O : Graph);
   --  Copy all edges from graph O to graph G.
   --
   --  Complexity is O(N).

   function Parent
     (G : Graph;
      V : Vertex_Id)
      return Vertex_Id
   with Pre => G.In_Neighbour_Count (V) = 1;
   --  Return the sole in neighbour of the vertex.
   --
   --  Complexity is O(1).

   function Child
     (G : Graph;
      V : Vertex_Id)
      return Vertex_Id
   with Pre  => G.Out_Neighbour_Count (V) = 1,
        Post => Child'Result /= Null_Vertex;
   --  Return the sole out neighbour of the vertex, which must exist
   --
   --  Complexity is O(1).

   function Num_Edges (G : Graph) return Natural;
   --  @param G a graph
   --  @return the number of edges in G

   ----------------------------------------------------------------------
   --  Clusters
   ----------------------------------------------------------------------

   procedure New_Cluster (G : in out Graph;
                          C :    out Cluster_Id)
   with Post => C /= Null_Cluster;
   --  Create a new cluster that vertices can be a member of.
   --
   --  Complexity is O(1).

   procedure Set_Cluster (G : in out Graph;
                          V : Vertex_Id;
                          C : Cluster_Id);
   --  Assigns the given cluster to the given vertex. Note a vertex can
   --  only be member of a single cluster, so any subsequent calls to
   --  Set_Cluster will override the old cluster.
   --
   --  Complexity is O(1).

   function Get_Cluster (G : Graph;
                         V : Vertex_Id)
                         return Cluster_Id;
   --  Returns the vertex' cluster.
   --
   --  Complexity is O(1).

   function Cluster_Hash (C : Cluster_Id) return Ada.Containers.Hash_Type;
   --  Hash a cluster_id

   ----------------------------------------------------------------------
   --  Iterators
   ----------------------------------------------------------------------

   function Get_Collection (G        : Graph;
                            V        : Vertex_Id;
                            The_Type : Vertex_Based_Collection)
                            return Vertex_Collection_T
   with Pre => V /= Null_Vertex;

   function Get_Collection (G        : Graph;
                            The_Type : Graph_Based_Collection)
                            return Vertex_Collection_T;

   function First_Cursor (Coll : Vertex_Collection_T)
                          return Cursor;

   function Next_Cursor (Coll : Vertex_Collection_T;
                         C    : Cursor)
                         return Cursor;

   function Has_Element (Coll : Vertex_Collection_T;
                         C    : Cursor)
                         return Boolean;

   function Get_Element (Coll : Vertex_Collection_T;
                         C    : Cursor)
                         return Vertex_Id;

   ----------------------------------------------------------------------
   --  Complex queries
   ----------------------------------------------------------------------

   function Non_Trivial_Path_Exists
     (G        : Graph;
      A        : Vertex_Id;
      B        : Vertex_Id;
      Reversed : Boolean := False)
      return Boolean
   with Pre => A /= Null_Vertex and B /= Null_Vertex;
   --  Checks if there is a non-trivial path from A to B. A trivial
   --  path, which is not allowed by this function, is for the special
   --  case where A = B and there is no edge from A to A.
   --
   --  If reversed is given then we operate on the reversed graph
   --  without actually reversing it. In particular this is much more
   --  efficient than first calling Invert and then calling this
   --  procedure on the reversed graph.
   --
   --  Complexity is O(N).

   function Non_Trivial_Path_Exists
     (G        : Graph;
      A        : Vertex_Id;
      F        : not null access function (V : Vertex_Id) return Boolean;
      Reversed : Boolean := False)
      return Boolean
   with Pre => A /= Null_Vertex;
   --  Checks if there is a non-trivial path from A to another vertex
   --  B for which F(B) holds.
   --
   --  If reversed is given then we operate on the reversed graph
   --  without actually reversing it. In particular this is much more
   --  efficient than first calling Invert and then calling this
   --  procedure on the reversed graph.
   --
   --  Complexity is O(N), assuming the complexity of F is O(1).

   ----------------------------------------------------------------------
   --  Visitors
   ----------------------------------------------------------------------

   procedure DFS
     (G             : Graph;
      Start         : Vertex_Id;
      Include_Start : Boolean;
      Visitor       : not null access procedure
        (V  : Vertex_Id;
         TV : out Simple_Traversal_Instruction);
      Edge_Selector : access function (A, B : Vertex_Id)
                                       return Boolean := null;
      Reversed      : Boolean := False)
   with Pre => Start /= Null_Vertex;
   --  Perform a depth-first search rooted at Start. If Include_Start
   --  is true, the first node visited is Start. If not, then Start is
   --  only visited if there is a non-trivial path from Start -> Start
   --  in the graph.
   --
   --  Visitor is called on each node V, which sets a traversal
   --  instruction which can be used to not traverse the children of
   --  node V. Note that any of these children could be reached by
   --  other paths.
   --
   --  If reversed is given then we operate on the reversed graph
   --  without actually reversing it. In particular this is much more
   --  efficient than first calling Invert and then calling DFS on the
   --  reversed graph.
   --
   --  Complexity is obviously O(N).

   procedure BFS
     (G             : Graph;
      Start         : Vertex_Id;
      Include_Start : Boolean;
      Visitor       : not null access procedure
        (V      : Vertex_Id;
         Origin : Vertex_Id;
         Depth  : Natural;
         T_Ins  : out Simple_Traversal_Instruction);
      Reversed      : Boolean := False)
   with Pre => Start /= Null_Vertex;
   --  Same as above, but perform a breadth first search instead.
   --
   --  Complexity is also O(N).

   procedure Shortest_Path
     (G             : Graph;
      Start         : Vertex_Id;
      Allow_Trivial : Boolean;
      Search        : not null access procedure
        (V           : Vertex_Id;
         Instruction : out Traversal_Instruction);
      Step          : not null access procedure (V : Vertex_Id);
      Reversed      : Boolean := False)
   with Pre => Start /= Null_Vertex;
   --  Search for a path rooted at node Start. If Allow_Trivial is
   --  True we begin by checking Start itself, otherwise Start is only
   --  checked if we reach it through an edge.
   --
   --  On each step of the search Search is called, which must return
   --  Found_Destination if we have found what we are looking for. The
   --  other traversal instructions can also be specified:
   --     * Continue        : Continue searching
   --     * Skip_Children   : Abort search and resume elsewhere
   --     * Abort_Traversal : Abort search
   --
   --  Reversed has the same meaning as it does for procedure DFS
   --  above.
   --
   --  Finally, if a path is found the Step procedure is called for
   --  each vertex on the path starting with Start and finally for the
   --  vertex Found_Destination was returned for. If step is never
   --  called there is no path.
   --
   --  Complexity is O(N).

   ----------------------------------------------------------------------
   --  Graph-wide operations
   ----------------------------------------------------------------------

   function Invert (G : Graph) return Graph;
   --  Creates a new graph with all edge directions reversed.
   --
   --  Complexity is, in theory, O(N^2). This worse-case requires
   --  every node to be connected to every other node.

   function Dominator_Tree
     (G : Graph;
      R : Vertex_Id) return Graph
   with Pre => R /= Null_Vertex;
   --  Computes the dominator tree of graph G rooted in R using the
   --  Lengauer-Tarjan dominator algorithm. This is the
   --  `sophisticated' implementation.
   --
   --  Complexity is O(M \alpha(N, M)) where:
   --     N is the number of vertices
   --     M is the number of edges
   --     \alpha is the functional inverse of Ackermann's function
   --
   --  If you don't want to look up \alpha, then the above is *better*
   --  than O(M log N), but worse than linear.

   function Dominance_Frontier
     (G : Graph;
      R : Vertex_Id) return Graph
   with Pre => R /= Null_Vertex;
   --  Computes the dominance frontier of graph G rooted in R using
   --  the `runner' algorithm by Ferrante, Harvey.
   --
   --  Complexity is O(N^2).
   --
   --  It may be interesting to point out that gcc also implements
   --  this in cfganal.c.

   procedure Close
     (G : in out Graph);
   --  Transitively close the graph using SIMPLE_TC from Nuutila's thesis
   --
   --  Complexity is O(N^2).

   function SCC
     (G : Graph)
      return Strongly_Connected_Components;
   --  Returns the condensation graph of G, i.e. a graph whose vertices are the
   --  strongly connected components of G and whose edges correspond to edges
   --  of G that connect vertices from different components. This graph can
   --  be used to quickly answer connectivity queries (just like Close), but
   --  without keeping the entire transitive closure of G in memory.

   ----------------------------------------------------------------------
   --  IO
   ----------------------------------------------------------------------

   type Node_Shape_T is
     (Shape_Oval,
      Shape_Box,
      Shape_Diamond,
      Shape_None);

   type Edge_Shape_T is (Edge_Normal);

   type Node_Display_Info is record
      Show        : Boolean;
      Shape       : Node_Shape_T;
      Colour      : Unbounded_String;
      Fill_Colour : Unbounded_String;
      Label       : Unbounded_String;
   end record;

   type Edge_Display_Info is record
      Show   : Boolean;
      Shape  : Edge_Shape_T;
      Colour : Unbounded_String;
      Label  : Unbounded_String;
   end record;

   procedure Write_Dot_File
     (G         : Graph;
      Filename  : String;
      Node_Info : not null access function (G : Graph;
                                            V : Vertex_Id)
                                            return Node_Display_Info;
      Edge_Info : not null access function (G      : Graph;
                                            A      : Vertex_Id;
                                            B      : Vertex_Id;
                                            Marked : Boolean;
                                            Colour : Edge_Colours)
                                            return Edge_Display_Info);
   --  Write the graph G in dot format to Filename, using supplied
   --  functions Node_Info and Edge_Info to pretty-print each vertex.

   procedure Write_Pdf_File
     (G         : Graph;
      Filename  : String;
      Node_Info : not null access function (G : Graph;
                                            V : Vertex_Id)
                                            return Node_Display_Info;
      Edge_Info : not null access function (G      : Graph;
                                            A      : Vertex_Id;
                                            B      : Vertex_Id;
                                            Marked : Boolean;
                                            Colour : Edge_Colours)
                                            return Edge_Display_Info);
   --  As above, but also generate a pdf file using dot.

   ----------------------------------------------------------------------
   --  Debug
   ----------------------------------------------------------------------

   function Vertex_To_Natural (G : Graph; V : Vertex_Id) return Natural;
   --  Debug function to get the internal index of the given vertex.

   function Cluster_To_Natural (G : Graph; C : Cluster_Id) return Natural;
   --  Debug function to get the internal index of the given cluster.

private

   ----------------------------------------------------------------------
   --  Vertex index stuff

   type Vertex_Id is new Natural;
   subtype Valid_Vertex_Id is Vertex_Id range 1 .. Vertex_Id'Last;

   Null_Vertex : constant Vertex_Id := 0;

   package VIL is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => Valid_Vertex_Id);
   use VIL;
   subtype Vertex_Index_List is VIL.Vector;

   package VIS is new Ada.Containers.Hashed_Sets
     (Element_Type        => Vertex_Id,
      Hash                => Vertex_Hash,
      Equivalent_Elements => "=");
   use VIS;
   subtype Vertex_Index_Set is VIS.Set;

   ----------------------------------------------------------------------
   --  Edge stuff

   type Edge_Attributes is record
      Marked : Boolean;
      Colour : Edge_Colours;
   end record;

   package EAM is new Ada.Containers.Hashed_Maps
     (Key_Type        => Valid_Vertex_Id,
      Element_Type    => Edge_Attributes,
      Hash            => Vertex_Hash,
      Equivalent_Keys => "=");
   use EAM;
   subtype Edge_Attribute_Map is EAM.Map;

   ----------------------------------------------------------------------
   --  Cluster stuff

   type Cluster_Id is new Natural;

   Null_Cluster : constant Cluster_Id := 0;

   ----------------------------------------------------------------------
   --  Graph stuff

   type Vertex is record
      Key            : Vertex_Key;
      In_Neighbours  : Vertex_Index_Set;
      Out_Neighbours : Edge_Attribute_Map;
      Cluster        : Cluster_Id;
   end record;

   package VL is new Ada.Containers.Vectors
     (Index_Type   => Valid_Vertex_Id,
      Element_Type => Vertex);
   use VL;
   subtype Vertex_List is VL.Vector; --  Vertex_Vector???

   package Key_To_Id_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Vertex_Key,
      Element_Type    => Vertex_Id,
      Hash            => Key_Hash,
      Equivalent_Keys => Test_Key,
      "="             => "=");

   type Graph is tagged record
      Vertices       : Vertex_List;
      Default_Colour : Edge_Colours;
      Frozen         : Boolean;
      Clusters       : Cluster_Id;
      Key_To_Id      : Key_To_Id_Maps.Map;
   end record;

   ----------------------------------------------------------------------
   --  Collections

   type Vertex_Collection_T (The_Type : Collection_Type_T) is record
      The_Graph : access constant Graph;
      case The_Type is
         when Vertex_Based_Collection =>
            Id : Vertex_Id;
         when Graph_Based_Collection =>
            null;
      end case;
   end record;

   type Cursor (Collection_Type : Collection_Type_T) is record
      case Collection_Type is
         when In_Neighbours =>
            VIS_Native_Cursor : VIS.Cursor;
         when Out_Neighbours =>
            EAM_Native_Cursor : EAM.Cursor;
         when All_Vertices =>
            VL_Native_Cursor : VL.Cursor;
      end case;
   end record;

   ----------------------------------------------------------------------
   --  Strongly connected components

   type Component_Id is new Positive;
   --  Identifier of a strongly connected component

   function Hash (C : Component_Id) return Ada.Containers.Hash_Type;

   package Vertex_To_Component_Vectors is new
     Ada.Containers.Vectors (Index_Type   => Valid_Vertex_Id,
                             Element_Type => Component_Id);

   package Component_Sets is new
     Ada.Containers.Hashed_Sets (Element_Type        => Component_Id,
                                 Hash                => Hash,
                                 Equivalent_Elements => "=");

   package Component_To_Components_Vectors is new
     Ada.Containers.Vectors (Index_Type   => Component_Id,
                             Element_Type => Component_Sets.Set,
                             "="          => Component_Sets."=");

   type Strongly_Connected_Components is record
      Vertex_To_Component : Vertex_To_Component_Vectors.Vector;
      Component_Graph     : Component_To_Components_Vectors.Vector;
   end record;
   --  The strongly connected components are represented as a map from original
   --  vertices to their strongly connected component and a map from one
   --  strongly connected component to others.

end Graphs;
