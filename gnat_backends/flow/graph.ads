------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                G R A P H                                 --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013, Altran UK Limited                   --
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
with Ada.Iterator_Interfaces;

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
--     * Transitive closure could improved by implementing the
--       STACK_TC algorithm, but as it requires a topological sort it
--       is significantly more difficult to implement. We only rarely
--       require transitive closure in release 1, in self-recursive
--       programs, hence there is no urgency.
--
--  A few other implementation notes:
--
--     * The iterator scheme is fairly complex and could be
--       improved. In particular it would be nice if we didn't have to
--       pass around a pointer.
--
--     * DFS could be implemented as an iterator.

generic
   type Vertex_Key is private;
   type Vertex_Attributes is private;
   with function Test_Key (A, B : Vertex_Key) return Boolean;
package Graph
is
   type T is tagged private;

   type Vertex_Id is private;
   Null_Vertex : constant Vertex_Id;

   type Collection_Type_T is (
                              --  Collections based on a vertex.
                              Out_Neighbours,
                              In_Neighbours,

                              --  Collections over the graph.
                              All_Vertices);
   subtype Vertex_Based_Collection is Collection_Type_T
     range Out_Neighbours .. In_Neighbours;
   subtype Graph_Based_Collection is Collection_Type_T
     range All_Vertices .. All_Vertices;

   type Vertex_Collection_T is tagged private
     with Default_Iterator  => Iterate,
          Iterator_Element  => Vertex_Id,
          Constant_Indexing => Get_Current_Vertex_Id;

   type Cursor (Collection_Type : Collection_Type_T) is private;

   type Traversal_Instruction is (Continue, Skip_Children);

   ----------------------------------------------------------------------
   --  Basic operations
   ----------------------------------------------------------------------

   function Create return T;
   --  Creates a new, empty graph.

   function Create (G : T'Class) return T;
   --  Creates a new graph with all the vertices from G, but no edges.

   ----------------------------------------------------------------------
   --  Vertex operations
   ----------------------------------------------------------------------

   --  Please note there is no Remove_Vertex, this is not an accident
   --  as it is not needed. It would also not be possible to
   --  implement.
   --
   --  As a consequence all vertex ids are valid for the lifetime of
   --  the graph object.

   function Get_Vertex (G : T'Class;
                        V : Vertex_Key)
                       return Vertex_Id;
   --  Search the vertex group for the given vertex and return its
   --  Id. If not found, a value outside the range of Valid_Vertex_Id
   --  is returned.
   --
   --  Complexity is O(N).

   function Get_Key (G : T'Class;
                     V : Vertex_Id)
                    return Vertex_Key
     with Pre => V /= Null_Vertex;
   --  Obtain the key for the given vertex.
   --
   --  Complexity is O(1).

   function Get_Attributes (G : T'Class;
                            V : Vertex_Id)
                           return Vertex_Attributes;
   --  Obtain the user-defined attributes of the given vertex.
   --
   --  Complexity is O(1).

   procedure Add_Vertex (G : in out T'Class;
                         V :        Vertex_Key;
                         A :        Vertex_Attributes)
     with Pre => G.Get_Vertex (V) = Null_Vertex;
   --  Add a new vertex to the graph, with no edges attached.
   --
   --  Complexity is O(1) in the general case, but presumably can be
   --  O(N) if the internal vector is resized.

   procedure Add_Vertex (G  : in out T'Class;
                         V  :        Vertex_Key;
                         A  :        Vertex_Attributes;
                         Id :    out Vertex_Id)
     with Pre  => G.Get_Vertex (V) = Null_Vertex,
          Post => Id /= Null_Vertex;
   --  As above but also return the new vertex id.

   ----------------------------------------------------------------------
   --  Edge operations
   ----------------------------------------------------------------------

   function Edge_Exists (G        : T'Class;
                         V_1, V_2 : Vertex_Id)
                        return Boolean;
   --  Tests if the given edge from V_1 to V_2 is in the graph.
   --
   --  Complexity is O(1).

   procedure Add_Edge (G        : in out T'Class;
                       V_1, V_2 :        Vertex_Id)
     with Pre  => V_1 /= Null_Vertex and
                  V_2 /= Null_Vertex,
          Post => G.Edge_Exists (V_1, V_2);
   --  Adds an unmarked edge from V_1 to V_2. If the edge already
   --  exists, we do nothing (i.e. existing edge attributes do not
   --  change).
   --
   --  Complexity is O(1).

   procedure Add_Edge (G        : in out T'Class;
                       V_1, V_2 :        Vertex_Key)
     with Pre  => G.Get_Vertex (V_1) /= Null_Vertex and
                  G.Get_Vertex (V_2) /= Null_Vertex,
          Post => G.Edge_Exists (G.Get_Vertex (V_1), G.Get_Vertex (V_2));
   --  Convenience function to add an edge between to vertices given
   --  by key (instead of id).
   --
   --  Complexity is O(N) due to Get_Vertex.

   procedure Remove_Edge (G        : in out T'Class;
                          V_1, V_2 :        Vertex_Id)
     with Pre  => V_1 /= Null_Vertex and
                  V_2 /= Null_Vertex,
          Post => not G.Edge_Exists (V_1, V_2);
   --  Removes the edge from V_1 to V_2 from the graph, if it exists.
   --
   --  Complexity is O(1).

   procedure Mark_Edge (G        : in out T'Class;
                        V_1, V_2 :        Vertex_Id)
     with Pre  => G.Edge_Exists (V_1, V_2),
          Post => G.Edge_Exists (V_1, V_2);
   --  Mark the edge from V_1 to V_2 in the graph.
   --
   --  Complexity is O(1).

   ----------------------------------------------------------------------
   --  Iterators
   ----------------------------------------------------------------------

   function Get_Collection (G        : access constant T'Class;
                            V        : Vertex_Id;
                            The_Type : Vertex_Based_Collection)
                           return Vertex_Collection_T'Class;

   function Get_Collection (G        : access constant T'Class;
                            The_Type : Graph_Based_Collection)
                           return Vertex_Collection_T'Class;

   function Has_Element (Pos : Cursor) return Boolean;

   package List_Iterators is new Ada.Iterator_Interfaces
     (Cursor, Has_Element);

   function Iterate (Container : Vertex_Collection_T)
                    return List_Iterators.Forward_Iterator'Class;

   function Get_Current_Vertex_Id (Container : Vertex_Collection_T;
                                   Pos       : Cursor)
                                  return Vertex_Id;

   ----------------------------------------------------------------------
   --  Visitors
   ----------------------------------------------------------------------

   procedure DFS (G             : T'Class;
                  Start         : Vertex_Id;
                  Include_Start : Boolean;
                  Visitor       : access procedure
                    (V  :     Vertex_Id;
                     TV : out Traversal_Instruction));
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
   --  Complexity is obviously O(N).

   ----------------------------------------------------------------------
   --  Graph-wide operations
   ----------------------------------------------------------------------

   function Invert (G : T'Class) return T;
   --  Creates a new graph with all edge directions reversed.
   --
   --  Complexity is, in theory, O(N^2). This worse-case requires
   --  every node to be connected to every other node.

   function Dominator_Tree (G : T'Class;
                            R : Vertex_Id)
                           return T
     with Pre => R /= Null_Vertex;
   --  Computes the dominator tree of graph G rooted in R using the
   --  Lengauer-Tarjan dominator algorithm. This is the
   --  `sophisticated' implementation.
   --
   --  Complexity is O(M \alpha(N, M)) where:
   --     N is the number of vertices
   --     M is the number of edges
   --     \alpha is the functional invers of Ackermann's function
   --
   --  If you don't want to look up \alpha, then the above is *better*
   --  than O(M log N), but worse than linear.

   function Dominance_Frontier (G : T'Class;
                                R : Vertex_Id)
                               return T;
   --  Computes the dominance frontier of graph G rooted in R using
   --  the `runner' algorithm by Ferrante, Harvey.
   --
   --  Complexity is O(N^2).
   --
   --  It may be interesting to point out that gcc also implements
   --  this in cfganal.c.

   procedure Close (G       : in out T'Class;
                    Visitor : access procedure (A, B : Vertex_Id));
   --  Transitively close the graph using SIMPLE_TC from Nuutila's
   --  thesis. The visitor procedure is called for each new edge added
   --  to the graph.
   --
   --  Complexity is O(N^2)

   ----------------------------------------------------------------------
   --  IO
   ----------------------------------------------------------------------

   procedure Write_Dot_File
     (G                   : T'Class;
      Filename            : String;
      Show_Solitary_Nodes : Boolean;
      PP                  : access function (V : Vertex_Key)
                                            return String);
   --  Write the graph G in dot (and pdf) format to Filename, using
   --  the PP function to pretty-print each vertex.

private

   ----------------------------------------------------------------------
   --  Vertex index stuff

   type Vertex_Id is new Natural;
   subtype Valid_Vertex_Id is Vertex_Id range 1 .. Vertex_Id'Last;

   Null_Vertex : constant Vertex_Id := 0;

   function Vertex_Index_Hash (Element : Vertex_Id)
                              return Ada.Containers.Hash_Type
     is (Ada.Containers.Hash_Type (Element));

   function Vertex_Index_Equiv (Left, Right : Vertex_Id)
                               return Boolean
     is (Left = Right);

   package VIL is new Ada.Containers.Vectors (Index_Type   => Positive,
                                              Element_Type => Valid_Vertex_Id);
   use VIL;
   subtype Vertex_Index_List is VIL.Vector;

   package VIS is new Ada.Containers.Hashed_Sets
     (Element_Type        => Vertex_Id,
      Hash                => Vertex_Index_Hash,
      Equivalent_Elements => Vertex_Index_Equiv);
   use VIS;
   subtype Vertex_Index_Set is VIS.Set;

   ----------------------------------------------------------------------
   --  Edge stuff

   type Edge_Attributes is record
      Marked : Boolean;
   end record;

   package EAM is new Ada.Containers.Hashed_Maps
     (Key_Type        => Valid_Vertex_Id,
      Element_Type    => Edge_Attributes,
      Hash            => Vertex_Index_Hash,
      Equivalent_Keys => Vertex_Index_Equiv);
   use EAM;
   subtype Edge_Attribute_Map is EAM.Map;

   ----------------------------------------------------------------------
   --  Graph stuff

   type Vertex is record
      Key            : Vertex_Key;
      Attributes     : Vertex_Attributes;
      In_Neighbours  : Vertex_Index_Set;
      Out_Neighbours : Edge_Attribute_Map;
   end record;

   package VL is new Ada.Containers.Vectors
     (Index_Type   => Valid_Vertex_Id,
      Element_Type => Vertex);
   use VL;
   subtype Vertex_List is VL.Vector;

   type T is tagged record
      Vertices : Vertex_List;
   end record;

   ----------------------------------------------------------------------
   --  Collections

   type Vertex_Collection_T is tagged record
      The_Type  : Collection_Type_T;
      The_Graph : access constant T'Class;
      Id        : Vertex_Id;
   end record;

   type Cursor (Collection_Type : Collection_Type_T) is record
      The_Collection : Vertex_Collection_T;
      case Collection_Type is
         when In_Neighbours =>
            VIS_Native_Cursor : VIS.Cursor;
         when Out_Neighbours =>
            EAM_Native_Cursor : EAM.Cursor;
         when All_Vertices =>
            VL_Native_Cursor : VL.Cursor;
      end case;
   end record;

end Graph;
