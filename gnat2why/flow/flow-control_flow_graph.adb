------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              F L O W . C O N T R O L _ F L O W _ G R A P H               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2013-2014, Altran UK Limited                 --
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

with Ada.Containers.Doubly_Linked_Lists;

with Errout;
with Namet;                              use Namet;
with Nlists;                             use Nlists;
with Sem_Eval;                           use Sem_Eval;
with Sem_Util;                           use Sem_Util;
with Sinfo;                              use Sinfo;
with Snames;                             use Snames;
with Stand;                              use Stand;

with Treepr;                             use Treepr;

with Flow_Debug;                         use Flow_Debug;
pragma Unreferenced (Flow_Debug);

with SPARK_Util;                         use SPARK_Util;
with SPARK_Definition;                   use SPARK_Definition;
with Why;
with Gnat2Why.Nodes;                     use Gnat2Why.Nodes;

with Flow.Antialiasing;                  use Flow.Antialiasing;
with Flow.Control_Flow_Graph.Utility;    use Flow.Control_Flow_Graph.Utility;
with Flow_Error_Messages;                use Flow_Error_Messages;
with Flow_Tree_Utility;                  use Flow_Tree_Utility;
with Flow_Utility.Initialization;        use Flow_Utility.Initialization;
with Flow_Utility;                       use Flow_Utility;

package body Flow.Control_Flow_Graph is

   use type Ada.Containers.Count_Type;

   use type Flow_Graphs.Vertex_Id;

   use Vertex_Sets;
   use type Flow_Id_Sets.Set;
   use type Node_Sets.Set;

   package Union_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Union_Id,
      "="          => "=");

   ------------------------------------------------------------
   --  Local types
   ------------------------------------------------------------

   ---------------------
   -- Connection_Maps --
   ---------------------

   --  The flow graph is produced using two datastructures,
   --  Graph_Connections and a map Union_Id -> Graph_Connections.
   --
   --  Any node in the AST may be represented by some vertices in the flow
   --  graph. For example if N is a N_Subprogram_Body and its
   --  Handled_Statement_Sequence contains the following statement:
   --
   --     if X > 0 then
   --        X := X - 1;
   --     else
   --        X := 0;
   --     end if;
   --
   --  Lets start at the bottom. We recurse down the tree and at some point
   --  we will call Do_Assignment_Statement for each of the two
   --  assignments. Every Do_FOOBAR procedure takes a FOOBAR node, and
   --  fills in the connection map for that node.
   --
   --  So, for the first assinment statement (assume this node is Ass_1 in
   --  the AST) we create a vertex (but no edges!) in the flow graph. We
   --  also create an entry in the connection map from Ass_1 to a
   --  connection map with the trivial "unit" connection.
   --
   --        GRAPH            CM
   --    0. [X := X - 1]      Ass_1 -> (0, {0})
   --
   --  (Where "0." is the vertex id of the node for "x := x - 1".) Each
   --  connection map captures a single entry vertex (0 in our example) and
   --  a set of exit vertices ({0} in our example). Read this as "control
   --  flow for the node Ass_1 is as follows: control goes into this vertex
   --  (0) we do one thing and control leaves this node again (0)".
   --
   --  Lets process the second assignment statement, our graph and
   --  connection map now looks like this:
   --
   --        GRAPH            CM
   --    0. [X := X - 1]      Ass_1 -> (0, {0})
   --    1. [X := 0]          Ass_2 -> (1, {1})
   --
   --  We now go up the tree and look at Do_If_Statement. First produce a
   --  vertex (it will be number "2".) in the graph for the N_If_Statement
   --  itself. We then assemble the connection map as follows:
   --
   --     - The entry point for the if statement is obviously the if
   --       statement itself (i.e. 2)
   --
   --     - We have two ways we can exit from the if statement S: we can
   --       fall off the end of the if branch (Then_Statements (S)) or the
   --       else branch (Else_Statements (S)). So the exits for the if
   --       statement X is the union of all exits of all branches.
   --
   --       To determine the exit of one of our branch we simply look into
   --       the connection map what is recorded for Then_Statements (S) and
   --       Else_Statements (S). In our case we get Ass_1 and Ass_2, but in
   --       real life you'd get some kind of List_Id.
   --
   --  So now our picture looks like this:
   --
   --        GRAPH            CM
   --    0. [X := X - 1]      Ass_1 -> (0, {0})
   --    1. [X := 0]          Ass_2 -> (1, {1})
   --    2. [if X > 0]        S     -> (2, {0, 1})
   --
   --  But wait, we still have not added any edges to the flow graph. We
   --  need to make sure that we have an edge from vertex 2 to entry of the
   --  Then_Statements (S) and an edge to the Else_Statements (S). The
   --  Do_If_Statement procedure will also call one of the Linkup
   --  procedures. These take essentially two argumens: A group of "from"
   --  points and a single target point and create edges from all "from" to
   --  the "to".
   --
   --  So, we will call:
   --     Linkup (2, connection_map[then_statements (s)].standard_entry)
   --     Linkup (2, connection_map[else_statements (s)].standard_entry)
   --
   --  And now our graph and connection map looks like this:
   --
   --        GRAPH                          CM
   --            2. [if X > 0]              Ass_1 -> (0, {0})
   --                /      \               Ass_2 -> (1, {1})
   --               /        \              S     -> (2, {0, 1})
   --              /          \
   --  0. [X := X - 1]     1. [X := 0]
   --
   --  Notice how the connection map was not changed by Linkup, but only
   --  the graph. The connection map for node N can be considered to be a
   --  "summary for node N and all child nodes".

   type Graph_Connections is record
      Standard_Entry : Flow_Graphs.Vertex_Id;
      Standard_Exits : Vertex_Sets.Set;
   end record;

   No_Connections : constant Graph_Connections :=
     Graph_Connections'(Standard_Entry => Flow_Graphs.Null_Vertex,
                        Standard_Exits => Vertex_Sets.Empty_Set);

   function Trivial_Connection (V : Flow_Graphs.Vertex_Id)
                               return Graph_Connections
   is (Graph_Connections'(Standard_Entry => V,
                          Standard_Exits => Vertex_Sets.To_Set (V)));
   --  Produce the trivial connection.

   function Union_Hash (X : Union_Id) return Ada.Containers.Hash_Type
   is (Ada.Containers.Hash_Type (abs (X)));

   package Connection_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Union_Id,
      Element_Type    => Graph_Connections,
      Hash            => Union_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   procedure Copy_Connections (CM  : in out Connection_Maps.Map;
                               Dst : Union_Id;
                               Src : Union_Id);
   --  Creats the connection map for Dst and copies all fields from Src to
   --  it.

   -------------
   -- Context --
   -------------

   --  The context is a bag of extra state that is passed around through
   --  each Do_* procedure.
   --
   --  Perhaps the most important aspect of the Context is the
   --  Folded_Function_Checks map, which is used to keep track of functions
   --  with dependency relations. The only reason to put a dependency
   --  relation on a function is to note that not all parameters have been
   --  used. For example:
   --
   --     function Multiply_After_Delay (A, B : Integer;
   --                                    W    : Float)
   --                                    return Integer
   --     with Depends => (Multiply_After_Delay'Result => (A, B),
   --                      null                        => W);
   --
   --  If such a function is used, we do not want W to flow into the final
   --  result of whatever it is doing, however this is difficult as
   --  functions are not really processed separately. Instead we are just
   --  interested in the "set of variables" present in an expression. So
   --  instead we have a parameter in Get_Variable_Set (Fold_Functions)
   --  which, if specified, will return simply the set {A, B} instead of
   --  {A, B, W} for expressions involving calls to Multiply_After_Delay.
   --
   --  However, we need to make sure that all variables are initialized
   --  when we call our function; but the generated vertex for an
   --  expression involving it no longer features W.
   --
   --  Hence, in all places where we call Get_Variable_Set and fold
   --  functions, we also remember the node_id of the expression. For
   --  example, if we have an if statement:
   --
   --     if Multiply_After_Delay (X, Y, Z) = 0 then
   --        ...
   --
   --  Lets assume the node_id for the statement is 42, and the node_id for
   --  Condition (42) is 88. When we process Get_Variable_Set (88), we
   --  place the following into the Folded_Function_Checks map:
   --
   --     42 -> {88}
   --
   --  At the end of Process_Statement we then re-check each of these
   --  expression and emit a sink vertex in front of the original vertex to
   --  check only the "unused" variables.
   --
   --  Inspect the graphs generated for test M412-008 for more information.
   --
   --  Finally we take a note of all vertices that are linked directly
   --  to the Helper_End_Vertex because they belong to a non-returning
   --  procedure. Vertices of this kind that lie within dead code will
   --  have to be unlinked at the end.

   type Context is record
      Current_Loops          : Node_Sets.Set;
      --  The set of loops currently processed. The innermost loop
      --  currently processed is Active_Loop.

      Active_Loop            : Entity_Id;
      --  The currently processed loop. This is always a member of
      --  Current_Loops, unless no loop is currently processed.

      Entry_References       : Node_Graphs.Map;
      --  A map from loops -> 'loop_entry references.

      Folded_Function_Checks : Node_Graphs.Map;
      --  A set of nodes we need to separately check for uninitialized
      --  variables due to function folding.

      No_Return_Vertices     : Vertex_Sets.Set;
      --  A set of vertices that are linked directly to the
      --  Helper_End_Vertex because they belong to a non-returning
      --  procedure.
   end record;

   No_Context : constant Context :=
     Context'(Current_Loops          => Node_Sets.Empty_Set,
              Active_Loop            => Empty,
              Entry_References       => Node_Graphs.Empty_Map,
              Folded_Function_Checks => Node_Graphs.Empty_Map,
              No_Return_Vertices     => Vertex_Sets.Empty_Set);

   ------------------------------------------------------------
   --  Local declarations
   ------------------------------------------------------------

   procedure Add_Vertex (FA : in out Flow_Analysis_Graphs;
                         F  : Flow_Id;
                         A  : V_Attributes);
   --  Helper function to add a vertex (with attributes) to the graph.

   procedure Add_Vertex (FA : in out Flow_Analysis_Graphs;
                         F  : Flow_Id;
                         A  : V_Attributes;
                         V  : out Flow_Graphs.Vertex_Id);
   --  Helper function to add a vertex (with attributes) to the graph,
   --  returning the Id of the newly added vertex.

   procedure Add_Vertex (FA : in out Flow_Analysis_Graphs;
                         A  : V_Attributes;
                         V  : out Flow_Graphs.Vertex_Id);
   --  Helper function to add an unkeyed vertex (with attributes) to the
   --  graph, returning its Id.

   procedure Linkup
     (CFG   : in out Flow_Graphs.T;
      Froms : Vertex_Sets.Set;
      To    : Flow_Graphs.Vertex_Id)
      with Pre => To /= Flow_Graphs.Null_Vertex;
   --  Link all vertices in Froms to the To vertex in the given graph.

   procedure Linkup
     (CFG   : in out Flow_Graphs.T;
      From  : Flow_Graphs.Vertex_Id;
      To    : Flow_Graphs.Vertex_Id)
      with Pre => From /= Flow_Graphs.Null_Vertex and
                  To   /= Flow_Graphs.Null_Vertex;
   --  Link the From to the To vertex in the given graph.

   procedure Join
     (FA    : in out Flow_Analysis_Graphs;
      CM    : in out Connection_Maps.Map;
      Nodes : Union_Lists.List;
      Block : out Graph_Connections);
   --  Join up the standard entry and standard exits of the given
   --  nodes. Block contains the combined standard entry and exits of
   --  the joined up sequence.

   procedure Create_Record_Tree
     (F        : Flow_Id;
      Leaf_Atr : V_Attributes;
      FA       : in out Flow_Analysis_Graphs);
   --  Create part of the tree structure used to represent records. In
   --  particular, we create the subtree which is formed by the leaf F
   --  up to the entire variable represented by F. In the art below
   --  the vertices marked with a * are created by this procedure if F
   --  is R.A.Y. If we come to a vertex which already exists, we
   --  stop. This means calling this procedure once for each leaf will
   --  eventually result in the entire tree.
   --
   --                  R*
   --                 / \
   --                /   \
   --             R.A*    R.B
   --            /   \
   --           /     \
   --      R.A.X       R.A.Y*

   procedure Create_Initial_And_Final_Vertices
     (E        : Entity_Id;
      Is_Param : Boolean;
      FA       : in out Flow_Analysis_Graphs);
   --  Create the 'initial and 'final vertices for the given entity
   --  and link them up to the start and end vertices.

   procedure Create_Initial_And_Final_Vertices
     (F             : Flow_Id;
      Mode          : Param_Mode;
      Uninitialized : Boolean;
      FA            : in out Flow_Analysis_Graphs);
   --  Create the 'initial and 'final vertices for the given global
   --  and link them up to the start and end vertices.

   procedure Do_Assignment_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Assignment_Statement;
   --  Process assignment statements. Pretty obvious stuff.

   procedure Do_Case_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Case_Statement;
   --  The CFG that we generate for case statements look like
   --  the following:
   --
   --                       case
   --                      / | | \
   --         ____________/  | |  \________________
   --        /           ___/   \_____             \
   --       /           /             \             \
   --      /            |              |             \
   --    when         when           when   (optional when others)
   --      |            |              |              |
   --      |            |              |              |
   --  when part    when part      when part      when part
   --      |            |              |              |
   --       \            \            /              /
   --        \            \___   ____/              /
   --         \_____________  | |  ________________/
   --                       | | | |
   --
   --  The standard exits of all parts feed into the standard
   --  exits of the entire case statement.

   procedure Do_Exit_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Exit_Statement;
   --  Deal with loop exit statements. We do this by actually finding
   --  the loop we are associated with and changing the connection map
   --  of that loop and not just our own. This procedure is somewhat
   --  unique as all others Do_XYZ procedures only ever deal with
   --  things pertaining to their given node.

   procedure Do_Extended_Return_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Extended_Return_Statement;
   --  The CFG that we generate for extended return statements looks
   --  like the following:
   --
   --  Returned_Object_Declaration
   --              |
   --  [Handled_Statement_Sequence]
   --              |
   --    return returned_object
   --              |
   --             end
   --
   --  We create a null vertex for the extended return statement (this
   --  vertex is not visible in the CFG).
   --
   --  The "return returned_object" vertex corresponds to the
   --  Return_Statement_Entity of the extended return, and its
   --  Aux_Node is set to the object actually returned (the
   --  N_Defining_Identifier node which has the Is_Return_Object flag
   --  set to True).
   --
   --  The Handled_Statement_Sequence is optional. All exits of the
   --  Handled_Statement_Sequence are gathered in the
   --  "return returned_object" vertex.

   procedure Do_Handled_Sequence_Of_Statements
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Handled_Sequence_Of_Statements;
   --  Simply calls Process_Statement_List.

   procedure Do_If_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_If_Statement;
   --  Deals with if statements. We generate a CFG which looks like
   --  this:
   --
   --  if
   --  | \
   --  |  if part
   --  |         \-----------------
   --  elsif                       \
   --  |    \                       |
   --  |     elsif part             |
   --  |               \---------   |
   --  elsif                     \  |
   --  |    \                     | |
   --  |     another elsif part   | |
   --  |                       \  | |
   --  (optional else part)     | | |

   procedure Do_Loop_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre  => Nkind (N) = N_Loop_Statement and then
                   Present (Identifier (N)),
           Post => Ctx.Current_Loops.Length = Ctx.Current_Loops'Old.Length;
   --  Deals with all three kinds of loops SPARK supports:
   --
   --     * for loops
   --     * while loops
   --     * (infinite) loops
   --
   --  Refer to the documentation of the nested procedures on how the
   --  constructed CFG will look like.
   --
   --  This will also update the information on variables modified by loops
   --  in Flow_Utility.

   procedure Do_Null_Or_Raise_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Null_Statement
                    or else Nkind (N) = N_Raise_Statement
                    or else Nkind (N) in N_Raise_xxx_Error;
   --  Deals with null and raise statements. We create a new vertex that has
   --  control flow in from the top and leave from the bottom (nothing happens
   --  in between).

   procedure Do_Object_Declaration
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Object_Declaration;
   --  Deal with declarations (with an optional initialization). We
   --  either generate a null vertex which is then stripped from the
   --  graph or a simple defining vertex. Additionally, if the
   --  object's type has a Default_Initial_Condition aspect, we check
   --  for uninitialized variables in the default initial condition.

   procedure Do_Package_Declaration
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Package_Declaration;
   --  When we find a nested package, we add 'initial and 'final
   --  vertices for all variables and state_abstractions it
   --  introduces.
   --
   --  For example, analysis of the following nested package:
   --
   --    package Inner
   --      with Abstract_State => (AS1, AS2),
   --           Initializes    => (AS1,
   --                              X => Foo,
   --                              Y => (Foo, Bar),
   --                              Z => Foo)
   --    is
   --       X : Integer := Foo;
   --       Y : Integer := X;
   --    end Inner;
   --
   --  would have the following effects:
   --
   --    1) Due to the Abstract_State aspect vertices AS1'Initial,
   --       AS1'Final, AS2'Initial and AS2'Final are created.
   --
   --    2) The visible part of package inner is analyzed as if it were
   --       part of the enclosing package. This means initial and final
   --       vertices for x, y, and z are introduced and two vertices for
   --       the two declarations.
   --
   --  Note that the initializes aspect is *not* considered yet, as it only
   --  holds once the package body has been elaborated. See
   --  Do_Package_Body_Or_Stub below for more information.

   procedure Do_Package_Body_Or_Stub
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) in N_Package_Body | N_Package_Body_Stub;
   --  When we find a nested package body, we bring its initializes clause
   --  to bear.
   --
   --  Lets remind ourselves of the example from Do_Package_Body:
   --
   --    package Inner
   --      with Abstract_State => (AS1, AS2),
   --           Initializes    => (AS1,
   --                              X => Foo,
   --                              Y => (Foo, Bar),
   --                              Z => Foo)
   --    is
   --       X : Integer := Foo;
   --       Y : Integer := X;
   --    end Inner;
   --
   --  Once we encounter the package body for Inner (or its stub), we know
   --  that the initializes contract has been fulfilled. We produce a
   --  vertex for each part of the initializes clause which models these
   --  dependencies. For the above example we have:
   --
   --    (AS1) | defines      : AS1
   --          | expl_depends : -
   --          | impl_depends : -
   --
   --    (X from Foo) | defines      : X
   --                 | expl_depends : Foo
   --                 | impl_depends : X
   --
   --  Note the implicit self-dependency on X here. We do this to make sure
   --  that the vertex for [x : integer := foo] is not ineffective.
   --
   --    (Y from Foo, Bar) | defines      : Y
   --                      | expl_depends : Foo, Bar
   --                      | impl_depends : Y
   --
   --    (Z from Foo) | defines      : Z
   --                 | expl_depends : Foo
   --                 | impl_depends : -
   --
   --  Note we do not have this self-dependency here, because Z is *not*
   --  initialized at specification.
   --
   --  Finally note that we never actually look into the nested package
   --  body (unlike its spec).

   procedure Do_Pragma
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Pragma;
   --  Deals with pragmas. We only check for uninitialized variables. We
   --  do not check for ineffective statements since all pragmas ought to
   --  be ineffective by definition.
   --
   --  We also make a note of any 'Loop_Entry references and store
   --  them in Ctx.Entry_References.
   --
   --  Please also see Pragma_Relevant_To_Flow which decides which
   --  pragmas are important.

   procedure Do_Precondition
     (Pre : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context);
   --  Deals with the given precondition expression.

   procedure Do_Procedure_Call_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Procedure_Call_Statement;
   --  Deal with procedure calls. We follow the ideas of the SDG paper
   --  by Horowitz, Reps and Binkley and have a separate vertex for
   --  each parameter (if a paramater is an in out, we have two
   --  vertices modelling it).
   --
   --  For a procedure P (A : in     Integer;
   --                     B : in out Integer;
   --                     C :    out Integer)
   --  we produce the following CFG when called as P (X, Y, Z):
   --
   --     call P
   --     |
   --     a_in := x
   --     |
   --     b_in := y
   --     |
   --     y := b_out
   --     |
   --     z := c_out
   --
   --  Globals are treated like parameters. Each of these vertices
   --  will also have call_vertex set in its attributes so that we can
   --  fiddle the CDG to look like this:
   --
   --                     call P
   --                    / |  | \
   --           --------/  |  |  ---------
   --          /           /  \           \
   --  a_in := x  b_in := y    y := b_out  z := c_out
   --
   --  Note that dependencies between the parameters are NOT set up
   --  here, this is done in Flow.Interprocedural. The vertex for call
   --  P will have IPFA set or not set, which changes how we fill in
   --  the dependencies. This decision is made in
   --  Control_Flow_Graph.Utility.

   procedure Do_Postcondition
     (Post : Node_Id;
      FA   : in out Flow_Analysis_Graphs;
      CM   : in out Connection_Maps.Map;
      Ctx  : in out Context);
   --  Deals with the given postcondition expression.

   procedure Do_Simple_Return_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Simple_Return_Statement;
   --  This deals with return statements (with and without an
   --  expression). They do not have a standard exit, instead we
   --  directly link them to the end vertex.

   procedure Do_Subprogram_Or_Block
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) in
        N_Subprogram_Body | N_Block_Statement | N_Package_Body;
   --  This is the top level procedure which deals with a subprogram,
   --  block or package elaboration statement. The declarations and
   --  sequence of statements is processed and linked.

   procedure Do_Type_Declaration
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) in N_Full_Type_Declaration | N_Subtype_Declaration;
   --  This ignores type declarations (but creates a sink vertex so we
   --  can check for use of uninitialized variables).

   procedure Process_Quantified_Expressions
     (L   : List_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context);
   --  This procedure goes through a given list of statements and
   --  recursively looks at each one, setting up the 'initial and
   --  'final vertices for symbols introduced by quantified
   --  expressions. We do not descend into nested subprograms.

   procedure Process_Quantified_Expressions
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context);
   --  As above but operates on a single node.

   procedure Process_Subprogram_Globals
     (Callsite : Node_Id;
      In_List  : in out Vertex_Vectors.Vector;
      Out_List : in out Vertex_Vectors.Vector;
      FA       : in out Flow_Analysis_Graphs;
      CM       : in out Connection_Maps.Map;
      Ctx      : in out Context);
   --  This procedures creates the in and out vertices for a
   --  subprogram's globals. They are not connected to anything,
   --  instead the vertices are added to the given in_list and
   --  out_list.

   procedure Process_Parameter_Associations
     (Callsite : Node_Id;
      In_List  : in out Vertex_Vectors.Vector;
      Out_List : in out Vertex_Vectors.Vector;
      FA       : in out Flow_Analysis_Graphs;
      CM       : in out Connection_Maps.Map;
      Ctx      : in out Context);
   --  Similar to the above procedure, this deals with the actuals
   --  provided in a subprogram call. The vertices are created but not
   --  linked up; as above they are added to in_list and out_list.

   procedure Process_Statement_List
     (L   : List_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context);
   --  This processes a list of statements and links up each statement
   --  to the its successor. The final connection map for L will map
   --  to the standard entry of the first statement and the standard
   --  exits of the last statement.

   procedure Process_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Post => Ctx'Old.Folded_Function_Checks.Length =
                Ctx.Folded_Function_Checks.Length;
   --  Process an arbitrary statement (this is basically a big case
   --  block which calls the various Do_XYZ procedures).

   function RHS_Split_Useful (N     : Node_Id;
                              Scope : Flow_Scope)
                              return Boolean
   with Pre => Nkind (N) in N_Assignment_Statement |
                            N_Object_Declaration
               and then Present (Expression (N));
   --  Checks the right hand side of an assignment statement (or the
   --  expression on an object declaration) and determines if we can to
   --  perform some meaningful record-field splitting.

   procedure Prune_Exceptional_Paths (FA : in out Flow_Analysis_Graphs);
   --  This procedure fulfils two purposes.
   --
   --  1) It removes:
   --       *  all vertices that inevitably lead to a raise statement,
   --          a statically-false assertion or a non-returning procedure
   --       *  all vertices that follow a raise statement, a
   --          statically-false assertion or a non-returning procedure
   --          that are not otherwise reachable from the start vertex.
   --
   --  2) It populates the Edges_To_Remove set of FA.

   procedure Simplify_CFG (FA : in out Flow_Analysis_Graphs);
   --  Remove all null vertices from the control flow graph.

   function Pragma_Relevant_To_Flow (N : Node_Id) return Boolean
     with Pre => Nkind (N) = N_Pragma;
   --  Check if flow analysis cares about this particular pragma.

   ------------------------------------------------------------
   --  Local procedures and functions
   ------------------------------------------------------------

   ----------------------
   -- Copy_Connections --
   ----------------------

   procedure Copy_Connections (CM  : in out Connection_Maps.Map;
                               Dst : Union_Id;
                               Src : Union_Id)
   is
      C : constant Graph_Connections := CM (Src);
   begin
      CM.Include (Dst, C);
   end Copy_Connections;

   ----------------
   -- Add_Vertex --
   ----------------

   procedure Add_Vertex (FA : in out Flow_Analysis_Graphs;
                         F  : Flow_Id;
                         A  : V_Attributes)
   is
      V : Flow_Graphs.Vertex_Id;
   begin
      FA.CFG.Add_Vertex (F, V);
      FA.Atr.Insert (V, A);
   end Add_Vertex;

   procedure Add_Vertex (FA : in out Flow_Analysis_Graphs;
                         F  : Flow_Id;
                         A  : V_Attributes;
                         V  : out Flow_Graphs.Vertex_Id)
   is
   begin
      FA.CFG.Add_Vertex (F, V);
      FA.Atr.Insert (V, A);
   end Add_Vertex;

   procedure Add_Vertex (FA : in out Flow_Analysis_Graphs;
                         A  : V_Attributes;
                         V  : out Flow_Graphs.Vertex_Id)
   is
   begin
      FA.CFG.Add_Vertex (V);
      FA.Atr.Insert (V, A);
   end Add_Vertex;

   --------------
   --  Linkup  --
   --------------

   procedure Linkup (CFG   : in out Flow_Graphs.T;
                     Froms : Vertex_Sets.Set;
                     To    : Flow_Graphs.Vertex_Id)
   is
   begin
      for From of Froms loop
         CFG.Add_Edge (From, To, EC_Default);
      end loop;
   end Linkup;

   procedure Linkup (CFG   : in out Flow_Graphs.T;
                     From  : Flow_Graphs.Vertex_Id;
                     To    : Flow_Graphs.Vertex_Id)
   is
   begin
      CFG.Add_Edge (From, To, EC_Default);
   end Linkup;

   ----------
   -- Join --
   ----------

   procedure Join
     (FA    : in out Flow_Analysis_Graphs;
      CM    : in out Connection_Maps.Map;
      Nodes : Union_Lists.List;
      Block : out Graph_Connections)
   is
      Prev : Union_Id;
      V    : Flow_Graphs.Vertex_Id;
   begin
      Block := No_Connections;

      Prev := Union_Id (Empty);
      for P of Nodes loop
         if Present (Node_Id (Prev)) then
            --  Connect this statement to the previous one.
            Linkup (FA.CFG,
                    CM (Prev).Standard_Exits,
                    CM (P).Standard_Entry);
         else
            --  This is the first vertex, so set the standard entry of
            --  the list.
            Block.Standard_Entry := CM (P).Standard_Entry;
         end if;

         Prev := P;
      end loop;

      if Present (Node_Id (Prev)) then
         --  Set the standard exits of the list, if we processed at
         --  least one element.
         Block.Standard_Exits := CM (Prev).Standard_Exits;
      else
         --  We had a null sequence so we need to produce a null node.
         Add_Vertex (FA, Null_Node_Attributes, V);
         Block.Standard_Entry := V;
         Block.Standard_Exits := To_Set (V);
      end if;
   end Join;

   ------------------------
   -- Create_Record_Tree --
   ------------------------

   procedure Create_Record_Tree
     (F        : Flow_Id;
      Leaf_Atr : V_Attributes;
      FA       : in out Flow_Analysis_Graphs) is
   begin
      if Is_Discriminant (F) then
         --  The discriminants do not live in the tree.
         return;
      end if;

      case F.Variant is
         when Normal_Use | In_View | Out_View =>
            raise Program_Error;

         when Initial_Value | Final_Value =>
            case F.Kind is
               when Null_Value =>
                  raise Program_Error;
               when Magic_String | Synthetic_Null_Export =>
                  null;
               when Direct_Mapping | Record_Field =>
                  if F.Kind = Record_Field
                    or else F.Facet in Private_Part | Extension_Part
                  then
                     declare
                        P : constant Flow_Id :=
                          Change_Variant (Parent_Record (F),
                                          Corresponding_Grouping (F.Variant));
                     begin
                        Create_Record_Tree (P, Leaf_Atr, FA);
                        Linkup (FA.CFG,
                                FA.CFG.Get_Vertex (P),
                                FA.CFG.Get_Vertex (F));
                     end;
                  end if;
            end case;

         when Initial_Grouping | Final_Grouping =>
            case F.Kind is
               when Null_Value =>
                  raise Program_Error;
               when Direct_Mapping | Record_Field =>
                  --  Only proceed if we don't have this vertex yet.
                  if FA.CFG.Get_Vertex (F) = Flow_Graphs.Null_Vertex then
                     --  Create vertex.
                     Add_Vertex
                       (FA,
                        F,
                        Make_Record_Tree_Attributes (Leaf_Atr));

                     if F.Kind = Record_Field then
                        Create_Record_Tree (Parent_Record (F), Leaf_Atr, FA);
                        Linkup (FA.CFG,
                                FA.CFG.Get_Vertex (Parent_Record (F)),
                                FA.CFG.Get_Vertex (F));
                     end if;
                  end if;
               when Magic_String | Synthetic_Null_Export =>
                  null;
            end case;
      end case;
   end Create_Record_Tree;

   ---------------------------------------
   -- Create_Initial_And_Final_Vertices --
   ----------------------------------------

   procedure Create_Initial_And_Final_Vertices
     (E        : Entity_Id;
      Is_Param : Boolean;
      FA       : in out Flow_Analysis_Graphs)
   is
      M : Param_Mode;

      procedure Process (F : Flow_Id);

      -------------
      -- Process --
      -------------

      procedure Process (F : Flow_Id)
      is
         V : Flow_Graphs.Vertex_Id;
         A : V_Attributes;
      begin
         --  Setup the n'initial vertex. Note that initialization for
         --  variables is detected (and set) when building the flow graph
         --  for declarative parts.
         A := Make_Variable_Attributes (F_Ent => Change_Variant
                                          (F, Initial_Value),
                                        Mode  => M,
                                        E_Loc => E);
         Add_Vertex
           (FA,
            Change_Variant (F, Initial_Value),
            A,
            V);
         Linkup (FA.CFG, V, FA.Start_Vertex);

         Create_Record_Tree (Change_Variant (F, Initial_Value),
                             A,
                             FA);

         --  Setup the n'final vertex.
         Add_Vertex
           (FA,
            Change_Variant (F, Final_Value),
            Make_Variable_Attributes (F_Ent => Change_Variant
                                        (F, Final_Value),
                                      Mode  => M,
                                      E_Loc => E),
            V);
         Linkup (FA.CFG, FA.End_Vertex, V);

         FA.All_Vars.Include (F);
      end Process;

   begin
      if Ekind (E) = E_Constant and not FA.Local_Constants.Contains (E) then
         --  We ignore non-local constants (for now).
         return;
      end if;

      if Is_Param then
         case Ekind (E) is
            when E_Out_Parameter    => M := Mode_Out;
            when E_In_Out_Parameter => M := Mode_In_Out;
            when E_In_Parameter     => M := Mode_In;
            when others =>
               raise Program_Error;
         end case;
      else
         M := Mode_Invalid;
      end if;

      declare
         FS : constant Flow_Id_Sets.Set := Flatten_Variable (E, FA.B_Scope);
      begin
         for Tmp of FS loop
            Process (Tmp);
            if Has_Bounds (Tmp, FA.B_Scope) then
               Process (Tmp'Update (Facet => The_Bounds));
            end if;
         end loop;
      end;
   end Create_Initial_And_Final_Vertices;

   procedure Create_Initial_And_Final_Vertices
     (F             : Flow_Id;
      Mode          : Param_Mode;
      Uninitialized : Boolean;
      FA            : in out Flow_Analysis_Graphs)
   is
      procedure Process (F : Flow_Id);

      -------------
      -- Process --
      -------------

      procedure Process (F : Flow_Id)
      is
         A : V_Attributes;
         V : Flow_Graphs.Vertex_Id;
      begin
         --  Setup the n'initial vertex. Initialization is deduced from
         --  the mode.
         A := Make_Global_Variable_Attributes
           (F      => Change_Variant (F, Initial_Value),
            Mode   => Mode,
            Uninit => Uninitialized);
         Add_Vertex
           (FA,
            Change_Variant (F, Initial_Value),
            A,
            V);
         Linkup (FA.CFG, V, FA.Start_Vertex);

         Create_Record_Tree (Change_Variant (F, Initial_Value),
                             A,
                             FA);

         --  Setup the n'final vertex.
         Add_Vertex
           (FA,
            Change_Variant (F, Final_Value),
            Make_Global_Variable_Attributes
              (F    => Change_Variant (F, Final_Value),
               Mode => Mode),
            V);
         Linkup (FA.CFG, FA.End_Vertex, V);

         FA.All_Vars.Include (F);
      end Process;

      FS : Flow_Id_Sets.Set;

   begin
      FS := Flatten_Variable (F, FA.B_Scope);
      for Tmp of FS loop
         Process (Tmp);
         if Has_Bounds (Tmp, FA.B_Scope) then
            Process (Tmp'Update (Facet => The_Bounds));
         end if;
      end loop;
   end Create_Initial_And_Final_Vertices;

   -------------------------------
   --  Do_Assignment_Statement  --
   -------------------------------

   procedure Do_Assignment_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      Subprograms_Called : constant Node_Sets.Set :=
        Get_Function_Set (Expression (N));

      V     : Flow_Graphs.Vertex_Id;
      Verts : Vertex_Vectors.Vector := Vertex_Vectors.Empty_Vector;

      Partial         : Boolean;
      View_Conversion : Boolean;
      Map_Root        : Flow_Id;
   begin

      --  First we need to determine the root name where we assign to, and
      --  if this is a partial or full assignment. This mirror the
      --  beginning of Untangle_Assignment_Target.

      declare
         Unused : Node_Lists.List;
      begin
         Get_Assignment_Target_Properties
           (Name (N),
            Partial_Definition => Partial,
            View_Conversion    => View_Conversion,
            Map_Root           => Map_Root,
            Seq                => Unused);
      end;

      --  We have two likely scenarios: some kind of record assignment (in
      --  which case we try our best to dis-entangle the record fields so
      --  that information does not bleed all over the place) and the
      --  default case.

      if not Partial and then RHS_Split_Useful (N, FA.B_Scope) then
         declare
            M            : Flow_Id_Maps.Map;
            Output       : Flow_Id;
            Inputs       : Flow_Id_Sets.Set;
            All_Vertices : Vertex_Sets.Set  := Vertex_Sets.Empty_Set;
            Missing      : Flow_Id_Sets.Set;
         begin
            M := Untangle_Record_Assignment
              (Expression (N),
               Map_Root                     => Map_Root,
               Map_Type                     => Get_Full_Type (Name (N),
                                                              FA.B_Scope),
               Scope                        => FA.B_Scope,
               Local_Constants              => FA.Local_Constants,
               Fold_Functions               => True,
               Use_Computed_Globals         => not FA.Compute_Globals,
               Expand_Synthesized_Constants => False);

            Missing := Flatten_Variable (Map_Root, FA.B_Scope);

            --  Split out the assignment over a number of vertices.
            for C in M.Iterate loop
               Output := Flow_Id_Maps.Key (C);
               Inputs := Flow_Id_Maps.Element (C);

               Missing.Delete (Output);

               Add_Vertex
                 (FA,
                  Make_Basic_Attributes
                    (Var_Def    => Flow_Id_Sets.To_Set (Output),
                     Var_Ex_Use => Inputs,
                     Sub_Called => Subprograms_Called,
                     Loops      => Ctx.Current_Loops,
                     E_Loc      => N,
                     Print_Hint => Pretty_Print_Record_Field),
                  V);
               Verts.Append (V);
               All_Vertices.Insert (V);
            end loop;

            if not View_Conversion then
               --  There might be some fields missing, but if this is not a
               --  view conversion (and we have already established its a
               --  full assignment), flow analysis must not claim any other
               --  fields are "uninitialized".
               for F of Missing loop
                  Add_Vertex
                    (FA,
                     Make_Basic_Attributes
                       (Var_Def    => Flow_Id_Sets.To_Set (F),
                        Var_Ex_Use => Flow_Id_Sets.Empty_Set,
                        Sub_Called => Node_Sets.Empty_Set,
                        Loops      => Ctx.Current_Loops,
                        E_Loc      => N,
                        Print_Hint => Pretty_Print_Record_Field),
                     V);
                  Verts.Append (V);
                  All_Vertices.Insert (V);
               end loop;
            end if;

            declare
               C : Flow_Graphs.Cluster_Id;
            begin
               FA.CFG.New_Cluster (C);
               for V of All_Vertices loop
                  FA.Other_Fields.Insert
                    (V,
                     All_Vertices - Vertex_Sets.To_Set (V));
                  FA.CFG.Set_Cluster (V, C);
               end loop;
            end;
         end;
      else
         declare
            Vars_Defined : Flow_Id_Sets.Set;
            Vars_Used    : Flow_Id_Sets.Set;
            Vars_Proof   : Flow_Id_Sets.Set;
         begin
            --  Work out which variables we define.
            Untangle_Assignment_Target
              (N                    => Name (N),
               Scope                => FA.B_Scope,
               Local_Constants      => FA.Local_Constants,
               Use_Computed_Globals => not FA.Compute_Globals,
               Vars_Defined         => Vars_Defined,
               Vars_Used            => Vars_Used,
               Vars_Proof           => Vars_Proof,
               Partial_Definition   => Partial);

            --  Work out the variables we use. These are the ones already
            --  used by the LHS + everything on the RHS.
            Vars_Used.Union
              (Get_Variable_Set
                 (Expression (N),
                  Scope                => FA.B_Scope,
                  Local_Constants      => FA.Local_Constants,
                  Fold_Functions       => True,
                  Use_Computed_Globals => not FA.Compute_Globals));

            --  Any proof variables we need to check separately. We also
            --  need to check the RHS for proof variables.
            Ctx.Folded_Function_Checks (N).Insert (Expression (N));
            if not Vars_Proof.Is_Empty then
               Ctx.Folded_Function_Checks (N).Insert (Name (N));
            end if;

            --  Produce the vertex.
            Add_Vertex
              (FA,
               Direct_Mapping_Id (N),
               Make_Basic_Attributes
                 (Var_Def    => Vars_Defined,
                  Var_Ex_Use => Vars_Used,
                  Var_Im_Use => (if Partial
                                 then Vars_Defined
                                 else Flow_Id_Sets.Empty_Set),
                  Sub_Called => Subprograms_Called,
                  Loops      => Ctx.Current_Loops,
                  E_Loc      => N),
               V);
            Verts.Append (V);
         end;
      end if;

      --  Finally, we join up all the vertices we have produced and record
      --  update the connection map.

      if Verts.Is_Empty then
         pragma Assert (Is_Null_Record (Etype (Name (N))));
         --  Assigning null records does not produce any assignments, so we
         --  create a null vertex instead.
         Add_Vertex (FA,
                     Direct_Mapping_Id (N),
                     Null_Node_Attributes,
                     V);
         Verts.Append (V);
      end if;

      V := Flow_Graphs.Null_Vertex;
      for W of Verts loop
         if V /= Flow_Graphs.Null_Vertex then
            Linkup (FA.CFG, V, W);
         end if;
         V := W;
      end loop;

      CM.Include (Union_Id (N),
                  Graph_Connections'
                    (Standard_Entry => Verts.First_Element,
                     Standard_Exits => To_Set (Verts.Last_Element)));
   end Do_Assignment_Statement;

   -------------------------
   --  Do_Case_Statement  --
   -------------------------

   procedure Do_Case_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V, V_Alter  : Flow_Graphs.Vertex_Id;
      Alternative : Node_Id;
   begin
      --  We have a vertex V for the case statement itself
      Add_Vertex
        (FA,
         Direct_Mapping_Id (N),
         Make_Basic_Attributes
           (Var_Ex_Use => Get_Variable_Set
              (Expression (N),
               Scope                => FA.B_Scope,
               Local_Constants      => FA.Local_Constants,
               Fold_Functions       => True,
               Use_Computed_Globals => not FA.Compute_Globals),
            Sub_Called => Get_Function_Set (Expression (N)),
            Loops      => Ctx.Current_Loops,
            E_Loc      => N),
         V);
      Ctx.Folded_Function_Checks (N).Insert (Expression (N));
      CM.Include (Union_Id (N), No_Connections);
      CM (Union_Id (N)).Standard_Entry := V;

      Alternative := First (Alternatives (N));

      while Present (Alternative) loop
         --  We introduce a vertex V_Alter for each
         --  Case_Statement_Alternative and we link that to V.
         Add_Vertex
           (FA,
            Direct_Mapping_Id (Alternative),
            Make_Aux_Vertex_Attributes (E_Loc => Alternative),
            V_Alter);
         Linkup (FA.CFG, V, V_Alter);

         --  We link V_Alter with its statements
         Process_Statement_List (Statements (Alternative), FA, CM, Ctx);
         Linkup (FA.CFG,
                 V_Alter,
                 CM (Union_Id (Statements (Alternative))).Standard_Entry);
         CM (Union_Id (N)).Standard_Exits.Union
           (CM (Union_Id (Statements (Alternative))).Standard_Exits);

         Next (Alternative);
      end loop;
   end Do_Case_Statement;

   -------------------------
   --  Do_Exit_Statement  --
   -------------------------

   procedure Do_Exit_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V : Flow_Graphs.Vertex_Id;
      L : Node_Id := N;
   begin
      --  Go up the tree until we find the loop we are exiting from.
      if not Present (Name (N)) then
         --  We just need to find the enclosing loop.
         loop
            L := Parent (L);
            exit when Nkind (L) = N_Loop_Statement;
         end loop;
      else
         --  We have a named loop, which we need to find.
         loop
            L := Parent (L);
            exit when Nkind (L) = N_Loop_Statement and then
              Entity (Identifier (L)) = Entity (Name (N));
         end loop;
      end if;

      --  Conditional and unconditional exits are different. One
      --  requires an extra vertex, the other does not.
      if not Present (Condition (N)) then
         Add_Vertex (FA,
                     Direct_Mapping_Id (N),
                     Null_Node_Attributes,
                     V);
         CM.Include (Union_Id (N),
                     Graph_Connections'
                       (Standard_Entry => V,
                        Standard_Exits => Vertex_Sets.Empty_Set));

         CM (Union_Id (L)).Standard_Exits.Include (V);

      else
         Add_Vertex
           (FA,
            Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Var_Ex_Use => Get_Variable_Set
                 (Condition (N),
                  Scope                => FA.B_Scope,
                  Local_Constants      => FA.Local_Constants,
                  Fold_Functions       => True,
                  Use_Computed_Globals => not FA.Compute_Globals),
               Sub_Called => Get_Function_Set (Condition (N)),
               Loops      => Ctx.Current_Loops,
               E_Loc      => N),
            V);
         Ctx.Folded_Function_Checks (N).Insert (Condition (N));
         CM.Include (Union_Id (N),
                     Trivial_Connection (V));

         CM (Union_Id (L)).Standard_Exits.Include (V);
      end if;
   end Do_Exit_Statement;

   ----------------------------------
   -- Do_Extended_Return_Statement --
   ----------------------------------

   procedure Do_Extended_Return_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V            : Flow_Graphs.Vertex_Id;
      Ret_Object_L : constant List_Id := Return_Object_Declarations (N);
      Ret_Entity   : constant Node_Id := Return_Statement_Entity (N);
      Ret_Object   : Node_Id;
   begin
      --  We create a null vertex for the extended return statement
      Add_Vertex
        (FA,
         Direct_Mapping_Id (N),
         Null_Node_Attributes,
         V);
      --  Control flows in, but we do not flow out again.
      CM.Include (Union_Id (N),
                  Graph_Connections'(Standard_Entry => V,
                                     Standard_Exits => Empty_Set));

      --  Go through Ret_Object_L list and locate Ret_Object
      Ret_Object := First (Ret_Object_L);
      while Nkind (Ret_Object) /= N_Object_Declaration
        or else not Is_Return_Object (Defining_Identifier (Ret_Object))
      loop
         Ret_Object := Next (Ret_Object);
         pragma Assert (Present (Ret_Object));
      end loop;
      Ret_Object := Defining_Identifier (Ret_Object);

      --  Process the statements of Ret_Object_L
      Process_Statement_List (Ret_Object_L, FA, CM, Ctx);

      --  Link the entry vertex V (the extended return statement) to
      --  standard entry of its return_object_declarations.
      Linkup (FA.CFG,
              V,
              CM (Union_Id (Ret_Object_L)).Standard_Entry);

      --  We create a vertex for the Return_Statement_Entity
      Add_Vertex
        (FA,
         Direct_Mapping_Id (Ret_Entity),
         Make_Extended_Return_Attributes
           (Var_Def         => Flatten_Variable (FA.Analyzed_Entity,
                                                 FA.B_Scope),
            Var_Use         => Flatten_Variable (Ret_Object,
                                                 FA.B_Scope),
            Object_Returned => Ret_Object,
            Sub_Called      => Get_Function_Set (Ret_Object),
            --  ??? really? I don't think we can call a function here...
            Loops           => Ctx.Current_Loops,
            E_Loc           => Ret_Entity),
         V);
      CM.Include (Union_Id (Ret_Entity), No_Connections);
      CM (Union_Id (Ret_Entity)).Standard_Entry := V;

      if Present (Handled_Statement_Sequence (N)) then
         declare
            Statement_Sequence : constant List_Id :=
              Statements (Handled_Statement_Sequence (N));
         begin
            --  We process the sequence of statements
            Process_Statement_List (Statement_Sequence, FA, CM, Ctx);
            --  We link the standard exits of Ret_Object_L to the standard
            --  entry of the sequence of statements.
            Linkup (FA.CFG,
                    CM (Union_Id (Ret_Object_L)).Standard_Exits,
                    CM (Union_Id (Statement_Sequence)).Standard_Entry);

            --  We link the standard exits of the sequence of
            --  statements to the standard entry of the implicit
            --  return statement.
            Linkup (FA.CFG,
                    CM (Union_Id (Statement_Sequence)).Standard_Exits,
                    V);
         end;
      else
         --  No sequence of statements is present. We link the
         --  standard exits of Ret_Object_L to the implicit return
         --  statement.
         Linkup (FA.CFG,
                 CM (Union_Id (Ret_Object_L)).Standard_Exits,
                 V);
      end if;

      --  We link the implicit return statement to the helper end vertex
      Linkup (FA.CFG, V, FA.Helper_End_Vertex);

   end Do_Extended_Return_Statement;

   -----------------------------------------
   --  Do_Handled_Sequence_Of_Statements  --
   -----------------------------------------

   procedure Do_Handled_Sequence_Of_Statements
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      Stmts : constant List_Id := Statements (N);
   begin
      Process_Statement_List (Stmts, FA, CM, Ctx);
      Copy_Connections (CM,
                        Dst => Union_Id (N),
                        Src => Union_Id (Stmts));
   end Do_Handled_Sequence_Of_Statements;

   -----------------------
   --  Do_If_Statement  --
   -----------------------

   procedure Do_If_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V, V_Prev       : Flow_Graphs.Vertex_Id;
      If_Part         : constant List_Id := Then_Statements (N);
      Else_Part       : constant List_Id := Else_Statements (N);
      Elsif_Part      : constant List_Id := Elsif_Parts (N);
      Elsif_Statement : Node_Id;
   begin
      --  We have a vertex for the if statement itself.
      Add_Vertex
        (FA,
         Direct_Mapping_Id (N),
         Make_Basic_Attributes
           (Var_Ex_Use => Get_Variable_Set
              (Condition (N),
               Scope                => FA.B_Scope,
               Local_Constants      => FA.Local_Constants,
               Fold_Functions       => True,
               Use_Computed_Globals => not FA.Compute_Globals),
            Sub_Called => Get_Function_Set (Condition (N)),
            Loops      => Ctx.Current_Loops,
            E_Loc      => N),
         V);
      Ctx.Folded_Function_Checks (N).Insert (Condition (N));
      CM.Include (Union_Id (N), No_Connections);
      CM (Union_Id (N)).Standard_Entry := V;

      --  We hang the if part off that.
      Process_Statement_List (If_Part, FA, CM, Ctx);
      Linkup (FA.CFG, V, CM (Union_Id (If_Part)).Standard_Entry);
      CM (Union_Id (N)).Standard_Exits.Union
        (CM (Union_Id (If_Part)).Standard_Exits);

      --  If we have elsif parts we chain them together in the obvious
      --  way:
      --
      --  if
      --  | \
      --  |  if part
      --  |         \-----------------
      --  elsif                       \
      --  |    \                       |
      --  |     elsif part             |
      --  |               \---------   |
      --  elsif                     \  |
      --  |    \                     | |
      --  |     another elsif part   | |
      --  |                       \  | |
      --  (optional else part)     | | |
      --
      --  The standard exits for all parts feed into the standard
      --  exits of the entire if statement.
      --
      --  Finally please note that at the end variable V is either the
      --  vertex for the if statement itself or the very last elsif
      --  part.

      if Elsif_Part /= No_List then
         Elsif_Statement := First (Elsif_Part);
         V_Prev          := V;

         while Present (Elsif_Statement) loop
            declare
               Elsif_Body : constant List_Id :=
                 Then_Statements (Elsif_Statement);
            begin
               --  We have a vertex V for each elsif statement, which we
               --  link to the previous one (V_Prev).
               Add_Vertex
                 (FA,
                  Direct_Mapping_Id (Elsif_Statement),
                  Make_Basic_Attributes
                    (Var_Ex_Use => Get_Variable_Set
                       (Condition (Elsif_Statement),
                        Scope                => FA.B_Scope,
                        Local_Constants      => FA.Local_Constants,
                        Fold_Functions       => True,
                        Use_Computed_Globals => not FA.Compute_Globals),
                     Sub_Called => Get_Function_Set (Condition
                                                       (Elsif_Statement)),
                     Loops      => Ctx.Current_Loops,
                     E_Loc      => Elsif_Statement),
                  V);
               Ctx.Folded_Function_Checks (N).Insert
                 (Condition (Elsif_Statement));
               Linkup (FA.CFG, V_Prev, V);

               Process_Statement_List (Elsif_Body, FA, CM, Ctx);
               Linkup (FA.CFG,
                       V,
                       CM (Union_Id (Elsif_Body)).Standard_Entry);
               CM (Union_Id (N)).Standard_Exits.Union
                 (CM (Union_Id (Elsif_Body)).Standard_Exits);
            end;

            V_Prev := V;
            Next (Elsif_Statement);
         end loop;
      end if;

      --  Remember that V is the vertex associated with either the
      --  last elsif blob or the if statement itself.

      if Else_Part /= No_List then
         Process_Statement_List (Else_Part, FA, CM, Ctx);
         Linkup (FA.CFG, V, CM (Union_Id (Else_Part)).Standard_Entry);
         CM (Union_Id (N)).Standard_Exits.Union
           (CM (Union_Id (Else_Part)).Standard_Exits);
      else
         CM (Union_Id (N)).Standard_Exits.Insert (V);
      end if;
   end Do_If_Statement;

   -------------------------
   --  Do_Loop_Statement  --
   -------------------------

   procedure Do_Loop_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      function Is_For_Loop (N : Node_Id) return Boolean
      is (Nkind (N) = N_Loop_Statement
            and then Present (Iteration_Scheme (N))
            and then Present (Loop_Parameter_Specification
                                (Iteration_Scheme (N))));
      --  Check if the given loop is a simlpe for loop.

      function Get_Loop_Variable (N : Node_Id) return Entity_Id
      is (Defining_Identifier
            (Loop_Parameter_Specification (Iteration_Scheme (N))))
      with Pre => Is_For_Loop (N);
      --  Obtain the entity of a for loops loop parameter.

      function Get_Loop_Name (N : Node_Id) return Entity_Id
      is (Entity (Identifier (N)));
      --  Obtain the entity of loop's label.

      function Get_Loop_Range (N : Node_Id) return Node_Id
      with Pre => Is_For_Loop (N);
      --  Return the range given for loop.

      function Loop_Might_Exit_Early (N : Node_Id) return Boolean;
      --  Return true if the loop contains an exit or return statement.

      procedure Do_Loop;
      --  Helper procedure to deal with normal loops.
      --
      --  We have two cases: Infinite loops and not-so-infinite loops.
      --
      --  For the infinite loop case we do not have exit or return
      --  statements in the loop. To get a mostly connected graph
      --  (there should be at least a path start -> end) we will
      --  pretend there is an "exit when False" statement at the end
      --  of the loop. Thus:
      --
      --        |
      --        +<----\
      --        |     |
      --        v     |
      --       BODY   |
      --        |  \--/
      --        v
      --
      --  If we would not do this we would get a null derives for the
      --  enclosing subprogram (along with some exceptions thrown by
      --  the dominator tree algorithm).
      --
      --  If we have at least one exit statement (for this loop) or a
      --  return statement we do not need to put in this faux exit.

      procedure Do_While_Loop;
      --  Helper procedure to deal with while loops.
      --
      --  This is actually the most simple of the loops. We generate
      --  the following graph:
      --
      --       |
      --       v
      --   CONDITION --\
      --   ^   |       |
      --   |   v       |
      --   |  BODY     |
      --   |   |       |
      --   \---/       v

      procedure Do_For_Loop (Fully_Initialized : out Flow_Id_Sets.Set);
      --  Helper procedure to deal with for loops.
      --
      --  We must distinguish between three kinds of for loops,
      --  depending on the range. It can be definitely empty,
      --  definitely non-empty and unknown.
      --
      --  For the "definitely empty" case we never connect the loop
      --  body:
      --
      --       |
      --       v
      --    PARAMETER         BODY
      --       |
      --       v
      --
      --  This will produce flow errors, which is what we want.
      --
      --  For the "unknown" case we have a construct similar to a
      --  while loop:
      --
      --       |
      --       v
      --   PARAMETER --\
      --   ^   |       |
      --   |   v       |
      --   |  BODY     |
      --   |   |       |
      --   \---/       v
      --
      --  This means the loop body may not be executed, so any
      --  initializations in the loop which subsequent code depends on
      --  will be flagged up.
      --
      --  Finally, for the "definitely non-empty" case we employ a
      --  creative hack. We move the parameter definition behind the
      --  loop body, which means there are no paths that never execute
      --  the loop. Any dependency on the parameter (for example if
      --  the user wrote range A .. B) is irrelevant as it must be
      --  static in the first place and thus there can't be any
      --  dependencies. Thus:
      --
      --        |
      --        v
      --       BODY <---\
      --        |       |
      --        v       |
      --    PARAMETER --/
      --        |
      --        v
      --
      --  The PARAMETER block defines the loop parameter (which is
      --  also flagged as Is_Initialized and Is_Loop_Parameter so that
      --  it can be suitably ignored by subsequent analysis).
      --
      --  We distinguish this case (non-empty range) from the previous
      --  one (unknown range) as subsequent code may rely on any
      --  initializations in the loop body.

      function Variables_Initialized_By_Loop (N : Node_Id)
                                              return Flow_Id_Sets.Set;
      --  A conservative heuristic to determine the set of possible
      --  variables fully initialized by the given statement list.

      --------------------
      -- Get_Loop_Range --
      --------------------

      function Get_Loop_Range (N : Node_Id) return Node_Id
      is
         DSD : constant Node_Id := Discrete_Subtype_Definition
           (Loop_Parameter_Specification (Iteration_Scheme (N)));

         R : Node_Id;
      begin
         case Nkind (DSD) is
            when N_Subtype_Indication =>
               case Nkind (Constraint (DSD)) is
                  when N_Range_Constraint =>
                     R := Range_Expression (Constraint (DSD));
                  when others =>
                     raise Why.Unexpected_Node;
               end case;
            when N_Identifier | N_Expanded_Name =>
               R := Get_Range (Entity (DSD));
            when N_Range =>
               R := DSD;
            when others =>
               Print_Node_Subtree (DSD);
               raise Why.Unexpected_Node;
         end case;
         return R;
      end Get_Loop_Range;

      -------------
      -- Do_Loop --
      -------------

      procedure Do_Loop is
         Contains_Return : Boolean := False;

         function Proc (N : Node_Id) return Traverse_Result;
         --  Set Contains_Return to true if we find a return statement.

         function Proc (N : Node_Id) return Traverse_Result
         is
         begin
            case Nkind (N) is
               when N_Simple_Return_Statement |
                 N_Extended_Return_Statement =>
                  Contains_Return := True;
                  return Abandon;
               when others =>
                  return OK;
            end case;
         end Proc;

         procedure Find_Return is new Traverse_Proc (Process => Proc);

         V           : Flow_Graphs.Vertex_Id;
         Faux_Exit_V : Flow_Graphs.Vertex_Id;

      begin
         --  Check if we have a return statement.
         Find_Return (N);

         --  We have a null vertex for the loop, as we have no
         --  condition.
         Add_Vertex (FA,
                     Direct_Mapping_Id (N),
                     Null_Node_Attributes,
                     V);

         --  Entry point for the loop is V.
         CM (Union_Id (N)).Standard_Entry := V;

         --  Exit from the loop is at the end of the loop, i.e. we are
         --  always going round at least once.
         if Contains_Return then
            --  If the loop contains a return statement we do not add
            --  the faux exit.
            null;
         elsif CM (Union_Id (N)).Standard_Exits.Length > 0 then
            --  If we already have a standard exit that means an exit
            --  statement added it. We don't need the faux exit.
            null;
         else
            --  We have neither return nor exit, so we simulate an
            --  "exit when false" at the end of the loop.

            --  We need a previously unused node, we can abuse the end
            --  label for this. This represents our "exit when false"
            --  node. We cannot just add a fake exit to the very last
            --  vertex in the loop body, as this introduces
            --  interesting (and unwanted) control dependencies on it.
            Add_Vertex
              (FA,
               Direct_Mapping_Id (End_Label (N)),
               Make_Aux_Vertex_Attributes (E_Loc     => N,
                                           Execution => Infinite_Loop),
               Faux_Exit_V);

            --  We now thread this at the back of the connection map
            --  for Statements (N). Sorry, this is really quite ugly.
            Linkup (FA.CFG,
                    CM (Union_Id (Statements (N))).Standard_Exits,
                    Faux_Exit_V);
            CM (Union_Id (Statements (N))).Standard_Exits :=
              Vertex_Sets.To_Set (Faux_Exit_V);

            --  Finally we add a mark the faux exit vertex as a
            --  possible exit of this loop.
            CM (Union_Id (N)).Standard_Exits.Include (Faux_Exit_V);
         end if;

         --  Loop the loop: V -> body -> V
         Linkup (FA.CFG, V, CM (Union_Id (Statements (N))).Standard_Entry);
         Linkup (FA.CFG, CM (Union_Id (Statements (N))).Standard_Exits, V);
      end Do_Loop;

      -------------------
      -- Do_While_Loop --
      -------------------

      procedure Do_While_Loop
      is
         V : Flow_Graphs.Vertex_Id;
      begin
         Add_Vertex
           (FA,
            Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Var_Ex_Use => Get_Variable_Set
                 (Condition (Iteration_Scheme (N)),
                  Scope                => FA.B_Scope,
                  Local_Constants      => FA.Local_Constants,
                  Fold_Functions       => True,
                  Use_Computed_Globals => not FA.Compute_Globals),
               Sub_Called => Get_Function_Set (Condition
                                                 (Iteration_Scheme (N))),
               Loops      => Ctx.Current_Loops,
               E_Loc      => N),
            V);
         Ctx.Folded_Function_Checks (N).Insert
           (Condition (Iteration_Scheme (N)));

         --  Flow for the while loops goes into the condition and then
         --  out again.
         CM (Union_Id (N)).Standard_Entry := V;
         CM (Union_Id (N)).Standard_Exits.Include (V);

         --  Loop the loop: V -> body -> V
         Linkup (FA.CFG, V, CM (Union_Id (Statements (N))).Standard_Entry);
         Linkup (FA.CFG, CM (Union_Id (Statements (N))).Standard_Exits, V);
      end Do_While_Loop;

      -----------------
      -- Do_For_Loop --
      -----------------

      procedure Do_For_Loop (Fully_Initialized : out Flow_Id_Sets.Set)
      is
         LPS : constant Node_Id :=
           Loop_Parameter_Specification (Iteration_Scheme (N));

         LP : constant Entity_Id := Defining_Identifier (LPS);

         DSD : constant Node_Id := Discrete_Subtype_Definition (LPS);

         R : constant Node_Id := Get_Loop_Range (N);
         V : Flow_Graphs.Vertex_Id;
      begin
         --  We have a new variable here which we have not picked up
         --  in Create, so we should set it up.
         Create_Initial_And_Final_Vertices (LP, False, FA);

         --  Work out which of the three variants (empty, full,
         --  unknown) we have...
         if Is_Null_Range (Low_Bound (R), High_Bound (R)) then
            --  We have an empty range. We should complain!
            Add_Vertex
              (FA,
               Direct_Mapping_Id (N),
               Make_Basic_Attributes
                 (Var_Def => Flatten_Variable (LP, FA.B_Scope),
                  Loops   => Ctx.Current_Loops,
                  E_Loc   => N),
               V);

            --  Flow goes into and out of the loop. Note that we do
            --  NOT hook up the loop body.
            CM (Union_Id (N)).Standard_Entry := V;
            CM (Union_Id (N)).Standard_Exits.Include (V);

            Fully_Initialized := Flow_Id_Sets.Empty_Set;

         elsif Not_Null_Range (Low_Bound (R), High_Bound (R)) then
            --  We need to make sure the loop is executed at least once.

            Add_Vertex
              (FA,
               Direct_Mapping_Id (N),
               Make_Basic_Attributes
                 (Var_Def => Flatten_Variable (LP, FA.B_Scope),
                  Loops   => Ctx.Current_Loops,
                  E_Loc   => N),
               V);

            --  Flow goes into the first statement and out the loop vertex.
            CM (Union_Id (N)).Standard_Entry :=
              CM (Union_Id (Statements (N))).Standard_Entry;
            CM (Union_Id (N)).Standard_Exits.Include (V);

            --  Loop the loop: V -> body -> V
            Linkup (FA.CFG, V, CM (Union_Id (Statements (N))).Standard_Entry);
            Linkup (FA.CFG, CM (Union_Id (Statements (N))).Standard_Exits, V);

            Fully_Initialized := Variables_Initialized_By_Loop (N);

         else
            --  We don't know if the loop will be executed or not.
            Add_Vertex
              (FA,
               Direct_Mapping_Id (N),
               Make_Basic_Attributes
                 (Var_Def    => Flatten_Variable (LP, FA.B_Scope),
                  Var_Ex_Use => Get_Variable_Set
                    (DSD,
                     Scope                => FA.B_Scope,
                     Local_Constants      => FA.Local_Constants,
                     Fold_Functions       => True,
                     Use_Computed_Globals => not FA.Compute_Globals),
                  Sub_Called => Get_Function_Set (DSD),
                  Loops      => Ctx.Current_Loops,
                  E_Loc      => N),
               V);
            Ctx.Folded_Function_Checks (N).Insert (DSD);

            --  Flow for the conditional for loop is like a while
            --  loop.
            CM (Union_Id (N)).Standard_Entry := V;
            CM (Union_Id (N)).Standard_Exits.Include (V);

            --  Loop the loop: V -> body -> V
            Linkup (FA.CFG, V, CM (Union_Id (Statements (N))).Standard_Entry);
            Linkup (FA.CFG, CM (Union_Id (Statements (N))).Standard_Exits, V);

            Fully_Initialized := Flow_Id_Sets.Empty_Set;
         end if;
      end Do_For_Loop;

      ---------------------------
      -- Loop_Might_Exit_Early --
      ---------------------------

      function Loop_Might_Exit_Early (N : Node_Id) return Boolean
      is
         Contains_Abort : Boolean := False;

         function Proc_Search (N : Node_Id) return Traverse_Result;

         function Proc_Search (N : Node_Id) return Traverse_Result
         is
         begin
            case Nkind (N) is
               when N_Simple_Return_Statement   |
                    N_Extended_Return_Statement |
                    N_Exit_Statement            =>
                  Contains_Abort := True;
                  return Abandon;
               when others =>
                  return OK;
            end case;
         end Proc_Search;

         procedure Do_Search is new Traverse_Proc (Proc_Search);
      begin
         Do_Search (N);
         return Contains_Abort;
      end Loop_Might_Exit_Early;

      -----------------------------------
      -- Variables_Initialized_By_Loop --
      -----------------------------------

      function Variables_Initialized_By_Loop (N : Node_Id)
                                              return Flow_Id_Sets.Set
      is
         Fully_Initialized : Flow_Id_Sets.Set :=
           Flow_Id_Sets.Empty_Set;

         type Target (Valid : Boolean := False)
            is record
               case Valid is
                  when True =>
                     Var : Flow_Id;
                     D   : Entity_Lists.Vector;
                  when False =>
                     null;
               end case;
            end record;
         Null_Target : constant Target := (Valid => False);

         function "=" (A, B : Target) return Boolean;

         function "=" (A, B : Target) return Boolean
         is
         begin
            if A.Valid /= B.Valid then
               return False;
            end if;

            if A.Valid then
               if not (A.Var = B.Var) then
                  return False;
               end if;

               if A.D.Length /= B.D.Length then
                  return False;
               end if;

               for I in Natural range 1 .. Natural (A.D.Length) loop
                  if A.D (I) /= B.D (I) then
                     return False;
                  end if;
               end loop;
            end if;

            return True;
         end "=";

         Current_Loop      : Node_Id         := Empty;
         Active_Loops      : Node_Sets.Set   := Node_Sets.Empty_Set;
         All_Loop_Vertices : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

         Lc : constant Graph_Connections := CM (Union_Id (N));

         function Get_Array_Index (N : Node_Id) return Target;
         --  Convert the target of an assignment to an array into a flow id
         --  and a list of indices.

         function Fully_Defined_In_Original_Loop (T : Target) return Boolean
         with Pre => T.Valid;
         --  Performs a mini-flow analysis on the current loop fragment to
         --  see if T is defined on all paths (but not explicitly used).

         function Proc_Search (N : Node_Id) return Traverse_Result;
         --  In the traversal of the loop body, this finds suitable targets
         --  and checks if they are fully initialized.

         procedure Rec (N : Node_Id);
         --  Wrapper around the traversal, so that Proc_Search can call
         --  itself.

         ---------------------
         -- Get_Array_Index --
         ---------------------

         function Get_Array_Index (N : Node_Id) return Target
         is
            F : Flow_Id;
            T : Entity_Id;
            L : Entity_Lists.Vector;
         begin
            --  First, is this really an array access?
            if Nkind (N) /= N_Indexed_Component then
               return Null_Target;
            end if;

            --  Does the Prefix chain only contain record fields?
            declare
               Ptr : Node_Id := Prefix (N);
            begin
               loop
                  case Nkind (Ptr) is
                     when N_Identifier | N_Expanded_Name =>
                        exit;
                     when N_Selected_Component =>
                        Ptr := Prefix (Ptr);
                     when others =>
                        return Null_Target;
                  end case;
               end loop;
            end;

            --  Construct the variable we're possibly fully defining.
            case Nkind (Prefix (N)) is
               when N_Identifier | N_Expanded_Name =>
                  F := Direct_Mapping_Id
                    (Unique_Entity (Entity (Prefix (N))));
                  T := Get_Full_Type (Entity (Prefix (N)),
                                      FA.B_Scope);

               when N_Selected_Component =>
                  F := Record_Field_Id (Prefix (N));
                  T := Get_Full_Type (Etype (Prefix (N)),
                                      FA.B_Scope);

               when others =>
                  raise Program_Error;
            end case;

            --  Extract indices (and make sure they are simple and
            --  distinct).
            L := Entity_Lists.Empty_Vector;
            declare
               Ptr         : Node_Id := First (Expressions (N));
               Index_Ptr   : Node_Id := First_Index (T);
               Param_Range : Node_Id;
               Index_Range : Node_Id;
            begin
               while Present (Ptr) loop
                  case Nkind (Ptr) is
                     when N_Identifier | N_Expanded_Name =>
                        if L.Contains (Entity (Ptr)) then
                           --  Non-distinct entry, just abort. For
                           --  example:
                           --
                           --  for I in Idx loop
                           --     A (I, I) := 0;
                           --  end loop;
                           return Null_Target;
                        end if;

                        if not Active_Loops.Contains (Entity (Ptr)) then
                           --  Not a loop variable we care about, again
                           --  we just abort. For example:
                           --
                           --  for I in Idx loop
                           --     A (J) := 0;
                           --  end loop;
                           return Null_Target;
                        end if;

                        Param_Range := Get_Range (Entity (Ptr));
                        Index_Range := Get_Range (Index_Ptr);

                        --  ??? Do we need to do something here for
                        --      static_predicate?
                        if not
                          (Compile_Time_Compare (Low_Bound (Param_Range),
                                                 Low_Bound (Index_Range),
                                                 True) = EQ and then
                             Compile_Time_Compare (High_Bound (Param_Range),
                                                   High_Bound (Index_Range),
                                                   True) = EQ)
                        then
                           --  The loop parameter type does not fully
                           --  cover this index type.
                           return Null_Target;
                        end if;

                        L.Append (Entity (Ptr));

                     when others =>
                        --  This is not a simple entity, so just abort.
                        --  For example:
                        --
                        --  for I in Idx loop
                        --     A (I + 1) := 0;
                        --  end loop;
                        return Null_Target;
                  end case;

                  Next (Ptr);
                  Next_Index (Index_Ptr);
               end loop;
            end;

            return (Valid => True,
                    Var   => F,
                    D     => L);
         end Get_Array_Index;

         ------------------------------------
         -- Fully_Defined_In_Original_Loop --
         ------------------------------------

         function Fully_Defined_In_Original_Loop (T : Target) return Boolean
         is
            Fully_Defined : Boolean         := True;
            Touched       : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

            procedure Check_Defined
              (V  : Flow_Graphs.Vertex_Id;
               Tv : out Flow_Graphs.Simple_Traversal_Instruction);
            --  Visitor to ensure all paths define T (and do not use it).

            procedure Check_Unused
              (V  : Flow_Graphs.Vertex_Id;
               Tv : out Flow_Graphs.Simple_Traversal_Instruction);
            --  Visitor to ensure all paths following a definition of T do
            --  not use it.

            procedure Check_Defined
              (V  : Flow_Graphs.Vertex_Id;
               Tv : out Flow_Graphs.Simple_Traversal_Instruction)
            is
               F : constant Flow_Id      := FA.CFG.Get_Key (V);
               A : constant V_Attributes := FA.Atr (V);
            begin
               Touched.Include (V);

               if A.Variables_Explicitly_Used.Contains (T.Var) then
                  Fully_Defined := False;
                  Tv            := Flow_Graphs.Abort_Traversal;

               elsif A.Variables_Defined.Contains (T.Var) and then
                 F.Kind = Direct_Mapping and then
                 Present (F.Node) and then
                 Nkind (F.Node) = N_Assignment_Statement and then
                 Get_Array_Index (Name (F.Node)) = T
               then
                  FA.CFG.DFS (Start         => V,
                              Include_Start => False,
                              Visitor       => Check_Unused'Access);
                  if Fully_Defined then
                     Tv := Flow_Graphs.Skip_Children;
                  else
                     Tv := Flow_Graphs.Abort_Traversal;
                  end if;

               elsif Lc.Standard_Exits.Contains (V) then
                  Fully_Defined := False;
                  Tv            := Flow_Graphs.Abort_Traversal;

               else
                  Tv := Flow_Graphs.Continue;
               end if;
            end Check_Defined;

            procedure Check_Unused
              (V  : Flow_Graphs.Vertex_Id;
               Tv : out Flow_Graphs.Simple_Traversal_Instruction)
            is
               --  F : constant Flow_Id      := FA.CFG.Get_Key (V);
               A : constant V_Attributes := FA.Atr (V);
            begin
               if Touched.Contains (V) then
                  Tv := Flow_Graphs.Skip_Children;
               elsif A.Variables_Explicitly_Used.Contains (T.Var) then
                  Fully_Defined := False;
                  Tv            := Flow_Graphs.Abort_Traversal;
               else
                  Tv := Flow_Graphs.Continue;
               end if;
            end Check_Unused;

         begin
            FA.CFG.DFS (Start         => Lc.Standard_Entry,
                        Include_Start => True,
                        Visitor       => Check_Defined'Access);

            return Fully_Defined;
         end Fully_Defined_In_Original_Loop;

         -----------------
         -- Proc_Search --
         -----------------

         function Proc_Search (N : Node_Id) return Traverse_Result is
         begin
            case Nkind (N) is
               when N_Loop_Statement =>
                  declare
                     Old_Loop : constant Node_Id := Current_Loop;
                  begin
                     if N = Current_Loop then
                        return OK;

                     elsif Is_For_Loop (N) then
                        Current_Loop := N;
                        Active_Loops.Insert (Get_Loop_Variable (N));

                        Rec (N);

                        Current_Loop := Old_Loop;
                        Active_Loops.Delete (Get_Loop_Variable (N));

                        return Skip;
                     end if;
                  end;

               when N_Assignment_Statement =>
                  declare
                     T : constant Target := Get_Array_Index (Name (N));
                  begin
                     if T.Valid
                       and then Fully_Defined_In_Original_Loop (T)
                     then
                        Fully_Initialized.Include (T.Var);
                     end if;
                  end;

               when N_Procedure_Call_Statement =>
                  --  ??? not done yet, we can implement this on demand

                  --  all out parameters (globals not relevant here)
                  null;

               when others =>
                  null;
            end case;
            return OK;
         end Proc_Search;
         procedure Rec_Inner is new Traverse_Proc (Proc_Search);

         ---------
         -- Rec --
         ---------

         procedure Rec (N : Node_Id)
         is
         begin
            Rec_Inner (N);
         end Rec;

      begin
         if Loop_Might_Exit_Early (N) then
            return Flow_Id_Sets.Empty_Set;
         end if;

         for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
            if FA.Atr (V).Loops.Contains (Get_Loop_Name (N)) then
               All_Loop_Vertices.Insert (V);
            end if;
         end loop;

         Rec (N);
         return Fully_Initialized;
      end Variables_Initialized_By_Loop;

      Loop_Id           : constant Entity_Id := Entity (Identifier (N));
      Fully_Initialized : Flow_Id_Sets.Set   := Flow_Id_Sets.Empty_Set;

   begin
      --  Start with a blank slate for the loops entry and exit.
      CM.Include (Union_Id (N), No_Connections);

      --  Construct graph for the loop body. Please note that early
      --  exists may alrady change the above, so be sure to only use
      --  union or include, instead of setting the standard exits.
      --
      --  We also change the context to include the current
      --  loop. Please note that we don't flag the loop statement
      --  itself as part of the loop, hence the corresponding delete
      --  is here as well.
      FA.Loops.Insert (Loop_Id);
      Ctx.Current_Loops.Insert (Loop_Id);
      Ctx.Entry_References.Include (Loop_Id, Node_Sets.Empty_Set);

      declare
         Tmp : constant Entity_Id := Ctx.Active_Loop;
      begin
         --  We can't use 'Update here as we may modify Ctx.
         Ctx.Active_Loop := Loop_Id;
         Process_Statement_List (Statements (N), FA, CM, Ctx);
         Ctx.Active_Loop := Tmp;
      end;

      if not Present (Iteration_Scheme (N)) then
         --  We have a loop.
         Do_Loop;

      else
         --  We have either a while loop or a for loop.

         --  We have a vertex for the loop condition, depending on its
         --  iteration scheme.
         if Present (Condition (Iteration_Scheme (N))) then
            --  We have a while loop.
            Do_While_Loop;

         elsif Present (Iterator_Specification (Iteration_Scheme (N))) then
            --  N_Iterator_Specification is not in SPARK2014
            raise Why.Not_SPARK;

         else
            --  We have a for loop. Make sure we don't have an
            --  iterator, but a normal range.
            pragma Assert (Present (Loop_Parameter_Specification (
                             Iteration_Scheme (N))));

            Do_For_Loop (Fully_Initialized);
         end if;
      end if;

      --  If we need an init vertex, we add it before the loop itself.
      if not Fully_Initialized.Is_Empty then
         declare
            V : Flow_Graphs.Vertex_Id;
         begin
            Add_Vertex
              (FA,
               Make_Basic_Attributes
                 (Var_Def    => Fully_Initialized,
                  Loops      => Ctx.Current_Loops,
                  E_Loc      => Loop_Id,
                  Print_Hint => Pretty_Print_Loop_Init)'
                 Update (Is_Program_Node => False),
               V);

            Linkup (FA.CFG, V, CM (Union_Id (N)).Standard_Entry);
            CM (Union_Id (N)).Standard_Entry := V;
         end;
      end if;

      --  Now we need to glue the 'loop_entry checks to the front of
      --  the loop.
      declare
         Augmented_Loop : Union_Lists.List := Union_Lists.Empty_List;
         V              : Flow_Graphs.Vertex_Id;
         Block          : Graph_Connections;
      begin
         --  We stick all loop entry references on a list of nodes.
         for Reference of Ctx.Entry_References (Loop_Id) loop
            Add_Vertex
              (FA,
               Direct_Mapping_Id (Reference),
               Make_Sink_Vertex_Attributes
                 (Var_Use       => Get_Variable_Set
                    (Prefix (Reference),
                     Scope                => FA.B_Scope,
                     Local_Constants      => FA.Local_Constants,
                     Fold_Functions       => False,
                     Use_Computed_Globals => not FA.Compute_Globals),
                  Is_Loop_Entry => True),
               V);
            Ctx.Folded_Function_Checks (N).Insert (Prefix (Reference));

            CM.Include
              (Union_Id (Reference),
               Trivial_Connection (V));

            Augmented_Loop.Append (Union_Id (Reference));
         end loop;

         --  Then we stick the actual loop at the end.
         Augmented_Loop.Append (Union_Id (N));

         --  And connect up the dots, and finally replacing the
         --  connection map we have for N with the new augmented one.
         Join (FA    => FA,
               CM    => CM,
               Nodes => Augmented_Loop,
               Block => Block);
         CM (Union_Id (N)) := Block;
      end;

      Ctx.Current_Loops.Delete (Loop_Id);

      --  Finally, we can update the loop information in Flow_Utility.

      Add_Loop (Loop_Id);
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         if FA.Atr (V).Loops.Contains (Loop_Id) then
            declare
               Combined_Writes : constant Flow_Id_Sets.Set :=
                 FA.Atr (V).Variables_Defined or FA.Atr (V).Volatiles_Read;
            begin
               for F of Combined_Writes loop
                  Add_Loop_Write (Loop_Id, F);
               end loop;
            end;
         end if;
      end loop;

   end Do_Loop_Statement;

   ----------------------------------
   --  Do_Null_Or_Raise_Statement  --
   ----------------------------------

   procedure Do_Null_Or_Raise_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      pragma Unreferenced (Ctx);
      V : Flow_Graphs.Vertex_Id;
   begin
      --  We introduce a vertex V which has control entering from the top and
      --  leaving from the bottom.
      Add_Vertex
        (FA,
         Direct_Mapping_Id (N),
         Make_Aux_Vertex_Attributes
           (E_Loc     => N,
            Execution => (if Nkind (N) = N_Raise_Statement or
                             Nkind (N) in N_Raise_xxx_Error
                          then Abnormal_Termination
                          else Normal_Execution)),
         V);
      CM.Include (Union_Id (N), Trivial_Connection (V));
   end Do_Null_Or_Raise_Statement;

   -----------------------------
   --  Do_Object_Declaration  --
   -----------------------------

   procedure Do_Object_Declaration
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      function Replace_Flow_Ids
        (Of_This   : Entity_Id;
         With_This : Entity_Id;
         The_Set   : Flow_Id_Sets.Set)
         return Flow_Id_Sets.Set;
      --  Returns a flow set that replaces all Flow_Ids of The_Set that
      --  correspond to Of_This with equivalent Flow_Ids that correspond to
      --  With_This.

      ----------------------
      -- Replace_Flow_Ids --
      ----------------------

      function Replace_Flow_Ids
        (Of_This   : Entity_Id;
         With_This : Entity_Id;
         The_Set   : Flow_Id_Sets.Set)
         return Flow_Id_Sets.Set
      is
         FS : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      begin
         for F of The_Set loop
            if F.Kind in Direct_Mapping | Record_Field
              and then F.Node = Of_This
            then
               FS.Include (F'Update (Node => With_This));
            else
               FS.Include (F);
            end if;
         end loop;
         return FS;
      end Replace_Flow_Ids;

      V     : Flow_Graphs.Vertex_Id;
      Inits : Vertex_Vectors.Vector := Vertex_Vectors.Empty_Vector;
      FS    : Flow_Id_Sets.Set;
   begin
      --  We are dealing with a local constant. These constants are *not*
      --  ignored.
      if Constant_Present (N) then
         if Present (Expression (N)) then
            FA.Local_Constants.Include (Defining_Identifier (N));
         else
            --  This is a deferred constant. We ignore it - we will deal
            --  with it once we get to the actual constant.
            --
            --  ??? What should we do if the private part is not in SPARK?
            Add_Vertex (FA,
                        Direct_Mapping_Id (N),
                        Null_Node_Attributes,
                        V);
            CM.Include (Union_Id (N), Trivial_Connection (V));
            return;
         end if;
      end if;

      --  First, we need a 'initial and 'final vertex for this object.
      Create_Initial_And_Final_Vertices (Defining_Identifier (N), False, FA);

      if not Present (Expression (N)) then
         --  No initializing expression, so we fall back to the
         --  default initialization (if any).
         FS := Flatten_Variable (Defining_Identifier (N), FA.B_Scope);

         for F of FS loop
            if Is_Default_Initialized (F) then
               Add_Vertex
                 (FA,
                  Make_Default_Initialization_Attributes
                    (FA    => FA,
                     Scope => FA.B_Scope,
                     F     => F,
                     Loops => Ctx.Current_Loops),
                  V);
               Inits.Append (V);
            end if;
         end loop;

         if Inits.Length = 0 then
            --  We did not have anything with a default initial value,
            --  so we just create a null vertex here.
            Add_Vertex (FA,
                        Direct_Mapping_Id (N),
                        Null_Node_Attributes,
                        V);
            Inits.Append (V);
         end if;

      else
         --  We have a variable declaration with an initialization.
         declare
            Var_Def : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
         begin
            FS := Flatten_Variable (Defining_Identifier (N), FA.B_Scope);
            for F of FS loop
               Var_Def.Include (F);
               if Has_Bounds (F, FA.B_Scope) then
                  Var_Def.Include (F'Update (Facet => The_Bounds));
               end if;
            end loop;

            if RHS_Split_Useful (N, FA.B_Scope) then

               declare
                  M : constant Flow_Id_Maps.Map := Untangle_Record_Assignment
                    (N                            => Expression (N),
                     Map_Root                     =>
                       Direct_Mapping_Id (Defining_Identifier (N)),
                     Map_Type                     =>
                       Get_Full_Type (Defining_Identifier (N), FA.B_Scope),
                     Scope                        => FA.B_Scope,
                     Local_Constants              => FA.Local_Constants,
                     Fold_Functions               => True,
                     Use_Computed_Globals         => not FA.Compute_Globals,
                     Expand_Synthesized_Constants => False);

                  Subprograms  : constant Node_Sets.Set :=
                    Get_Function_Set (Expression (N));

                  Output       : Flow_Id;
                  Inputs       : Flow_Id_Sets.Set;
                  All_Vertices : Vertex_Sets.Set  := Vertex_Sets.Empty_Set;
                  Missing      : Flow_Id_Sets.Set := Var_Def;
               begin

                  for C in M.Iterate loop
                     Output := Flow_Id_Maps.Key (C);
                     Inputs := Flow_Id_Maps.Element (C);

                     --  ??? It might be useful to improve E_Loc to point
                     --      at the relevant bit in the aggregate.

                     Add_Vertex
                       (FA,
                        Make_Basic_Attributes
                          (Var_Def    => Flow_Id_Sets.To_Set (Output),
                           Var_Ex_Use => Inputs,
                           Sub_Called => Subprograms,
                           Loops      => Ctx.Current_Loops,
                           E_Loc      => N,
                           Print_Hint => Pretty_Print_Record_Field),
                        V);
                     Missing.Delete (Output);

                     Inits.Append (V);
                     All_Vertices.Insert (V);
                  end loop;

                  --  Any "missing" fields which are produced by flatten,
                  --  but not by URA we flag as initialized to the empty
                  --  set; since it is not possible in SPARK to partially
                  --  initialize a variable at declaration.
                  for F of Missing loop
                     Add_Vertex
                       (FA,
                        Make_Basic_Attributes
                          (Var_Def    => Flow_Id_Sets.To_Set (F),
                           Var_Ex_Use => Flow_Id_Sets.Empty_Set,
                           Sub_Called => Node_Sets.Empty_Set,
                           Loops      => Ctx.Current_Loops,
                           E_Loc      => N,
                           Print_Hint => Pretty_Print_Record_Field),
                        V);
                     Inits.Append (V);
                     All_Vertices.Insert (V);
                  end loop;

                  declare
                     C : Flow_Graphs.Cluster_Id;
                  begin
                     FA.CFG.New_Cluster (C);
                     for V of All_Vertices loop
                        FA.Other_Fields.Insert
                          (V,
                           All_Vertices - Vertex_Sets.To_Set (V));
                        FA.CFG.Set_Cluster (V, C);
                     end loop;
                  end;
               end;

            else

               Add_Vertex
                 (FA,
                  Direct_Mapping_Id (N),
                  Make_Basic_Attributes
                    (Var_Def    => Var_Def,
                     Var_Ex_Use => Get_Variable_Set
                       (Expression (N),
                        Scope                => FA.B_Scope,
                        Local_Constants      => FA.Local_Constants,
                        Fold_Functions       => True,
                        Use_Computed_Globals => not FA.Compute_Globals),
                     Sub_Called => Get_Function_Set (Expression (N)),
                     Loops      => Ctx.Current_Loops,
                     E_Loc      => N),
                  V);
               Inits.Append (V);

            end if;

            Ctx.Folded_Function_Checks (N).Include (Expression (N));
         end;
      end if;

      --  If this type has a Default_Initial_Condition then we need to
      --  create a vertex to check for uninitialized variables within the
      --  Default_Initial_Condition's expression.
      declare
         Typ  : Node_Id;
         Expr : Node_Id;
      begin
         Typ := Etype (Defining_Identifier (N));

         if (Has_Default_Init_Cond (Typ)
               or else Has_Inherited_Default_Init_Cond (Typ))
           and then Present (Default_Init_Cond_Procedure (Typ))
         then
            Expr := Get_Expr_From_Check_Only_Proc
              (Default_Init_Cond_Procedure (Typ));

            if Present (Expr) then
               --  Note that default initial conditions make use of the
               --  type mark, i.e. Foo (T) > 2; so if we declare X : T we
               --  need to replace T with X to produce the correct default
               --  initial condition.
               Add_Vertex
                 (FA,
                  Make_Sink_Vertex_Attributes
                    (Var_Use    => Replace_Flow_Ids
                       (Of_This   => First_Entity (Default_Init_Cond_Procedure
                                                   (Typ)),
                        With_This => Defining_Identifier (N),
                        The_Set   => Get_Variable_Set
                          (Expr,
                           Scope                => FA.B_Scope,
                           Local_Constants      => FA.Local_Constants,
                           Fold_Functions       => True,
                           Use_Computed_Globals => not FA.Compute_Globals)),
                     Sub_Called => Get_Function_Set (Expr),
                     Is_Proof   => True,
                     Is_DIC     => True,
                     E_Loc      => N),
                  V);
               Inits.Append (V);

               --  Check for folded functions
               Ctx.Folded_Function_Checks (N).Include (Expr);
            end if;
         end if;
      end;

      V := Flow_Graphs.Null_Vertex;
      for W of Inits loop
         if V /= Flow_Graphs.Null_Vertex then
            Linkup (FA.CFG, V, W);
         end if;
         V := W;
      end loop;
      CM.Include (Union_Id (N),
                  Graph_Connections'
                    (Standard_Entry => Inits.First_Element,
                     Standard_Exits => To_Set (Inits.Last_Element)));

      if Ekind (FA.Analyzed_Entity) in E_Package | E_Package_Body then
         --  If we are analyzing a package body or spec and we just
         --  introduced 'Initial and 'Final vertices for an entity
         --  that is mentioned in an initializes aspect, we have
         --  to set Is_Export on the corresponding 'Final vertices.
         FS := Flatten_Variable (Defining_Identifier (N), FA.B_Scope);

         for F of FS loop
            declare
               Final_F_Id : constant Flow_Id :=
                 Change_Variant (F, Final_Value);

               Final_V_Id : constant Flow_Graphs.Vertex_Id :=
                 FA.CFG.Get_Vertex (Final_F_Id);
            begin
               if Final_V_Id /= Flow_Graphs.Null_Vertex then
                  declare
                     Final_Atr : V_Attributes := FA.Atr (Final_V_Id);

                     Entire_Var : constant Entity_Id := Final_F_Id.Node;
                  begin
                     Final_Atr.Is_Export := Final_Atr.Is_Export
                       or else Is_Initialized_At_Elaboration (Entire_Var,
                                                              FA.B_Scope);

                     FA.Atr (Final_V_Id) := Final_Atr;
                  end;
               end if;
            end;
         end loop;
      end if;
   end Do_Object_Declaration;

   ----------------------------
   -- Do_Package_Declaration --
   ----------------------------

   procedure Do_Package_Declaration
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      AS_Pragma : constant Node_Id :=
        Get_Pragma (Defining_Unit_Name (Specification (N)),
                    Pragma_Abstract_State);
   begin

      --  Introduce variables from the abstract state of the nested
      --  package.

      if Present (AS_Pragma) then
         declare
            PAA : Node_Id;
            AS  : Node_Id;
         begin
            PAA := First (Pragma_Argument_Associations (AS_Pragma));
            AS := First (Expressions (Expression (PAA)));
            while Present (AS) loop
               --  Creating 'Initial and 'Final vertices for every
               --  state abstraction and setting Is_Export to True
               --  if the corresponding entity is initialized.
               declare
                  New_E : constant Entity_Id :=
                    (if Nkind (AS) = N_Extension_Aggregate then
                       Entity (Ancestor_Part (AS))
                     else
                       Entity (AS));

                  Final_F_Id : constant Flow_Id :=
                    Change_Variant (Direct_Mapping_Id (New_E),
                                    Final_Value);

                  Final_V_Id : Flow_Graphs.Vertex_Id :=
                    FA.CFG.Get_Vertex (Final_F_Id);
               begin
                  --  Both the Refined_State aspect of the
                  --  Analyzed_Entity and the Abstract_State aspect of
                  --  the nested packages add vertices for state
                  --  abstractions so we have to be careful not to
                  --  add something that already exists.
                  if Final_V_Id = Flow_Graphs.Null_Vertex then

                     Create_Initial_And_Final_Vertices
                       (New_E,
                        Is_Param => False,
                        FA       => FA);

                     Final_V_Id := FA.CFG.Get_Vertex (Final_F_Id);

                     if Ekind (FA.Analyzed_Entity) in E_Package |
                                                      E_Package_Body
                     then
                        declare
                           Final_Atr  : V_Attributes := FA.Atr (Final_V_Id);
                        begin
                           Final_Atr.Is_Export := Final_Atr.Is_Export
                             or else Is_Initialized_At_Elaboration
                                       (New_E,
                                        FA.B_Scope);

                           FA.Atr (Final_V_Id) := Final_Atr;
                        end;
                     end if;
                  end if;
               end;

               Next (AS);
            end loop;
         end;
      end if;

      --  Traverse visible part of the specs.

      declare
         Visible_Part : constant List_Id :=
           Visible_Declarations (Specification (N));
      begin
         Process_Statement_List (Visible_Part, FA, CM, Ctx);

         Copy_Connections (CM,
                           Dst => Union_Id (N),
                           Src => Union_Id (Visible_Part));
      end;
   end Do_Package_Declaration;

   -----------------------------
   -- Do_Package_Body_Or_Stub --
   -----------------------------

   procedure Do_Package_Body_Or_Stub
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      function Find_Node (E : Entity_Id) return Node_Id
        with Post => Nkind (Find_Node'Result) in
                       N_Identifier           |
                       N_Expanded_Name        |
                       N_Component_Association;
      --  Looks through the initializes aspect on FA.Analyzed_Entity
      --  and returns the node which represents the
      --  initialization_item where E is the LHS.
      --
      --  In the case of
      --     Initializes => (X,
      --  we return the node for X (N_Identifier | N_Expanded_Name).
      --
      --  In the case of
      --     Initializes => (X => Y
      --  we return the node for => (N_Component_Association).

      Package_Spec : constant Entity_Id :=
        (case Nkind (N) is
            when N_Package_Body =>
               Corresponding_Spec (N),
            when N_Package_Body_Stub =>
               Corresponding_Spec_Of_Stub (N),
            when others =>
               raise Program_Error);

      Initializes_Aspect : constant Node_Id := Get_Pragma (Package_Spec,
                                                           Pragma_Initializes);

      ---------------
      -- Find_Node --
      ---------------

      function Find_Node (E : Entity_Id) return Node_Id is
         PAA_Expr : constant Node_Id :=
           Expression (First
                         (Pragma_Argument_Associations
                            (Initializes_Aspect)));
         Search : Node_Id;
      begin
         if Present (Expressions (PAA_Expr)) then
            Search := First (Expressions (PAA_Expr));
            while Present (Search) loop
               if Entity (Search) = E then
                  return Search;
               end if;

               Next (Search);
            end loop;
         end if;

         if Present (Component_Associations (PAA_Expr)) then
            declare
               CA : Node_Id;
            begin
               CA := First (Component_Associations (PAA_Expr));
               while Present (CA) loop
                  Search := First (Choices (CA));
                  if Entity (Search) = E then
                     return CA;
                  end if;

                  Next (CA);
               end loop;
            end;
         end if;

         --  We should never reach here!
         raise Program_Error;
      end Find_Node;

      DM : constant Dependency_Maps.Map :=
        (if Present (Initializes_Aspect)
         then Parse_Initializes (Initializes_Aspect)
         else Dependency_Maps.Empty_Map);

      V : Flow_Graphs.Vertex_Id;

   begin

      --  If we have no initialize aspect, then the package elaboration
      --  will have no observable effect in the enclosing package.

      if No (Initializes_Aspect) then
         Add_Vertex (FA, Direct_Mapping_Id (N), Null_Node_Attributes, V);
         CM.Include (Union_Id (N), Trivial_Connection (V));
         return;
      end if;

      pragma Assert_And_Cut (Present (Initializes_Aspect));

      --  When we encounter the package body (or its stub), we know that
      --  the package has been elaborated. We need to apply the initializes
      --  aspect at this point.

      declare
         Verts          : Union_Lists.List := Union_Lists.Empty_List;
         Initializes_CM : Graph_Connections;
      begin
         for C in DM.Iterate loop
            declare
               The_Out : constant Flow_Id := Dependency_Maps.Key (C);
               The_Ins : constant Flow_Id_Sets.Set :=
                 Dependency_Maps.Element (C);

               Init_Item : constant Node_Id :=
                 Find_Node (Get_Direct_Mapping_Id (The_Out));
            begin
               Verts.Append (Union_Id (Init_Item));

               Add_Vertex
                 (FA,
                  Direct_Mapping_Id (Init_Item),
                  Make_Package_Initialization_Attributes
                    (The_State => The_Out,
                     Inputs    => The_Ins,
                     Scope     => FA.B_Scope,
                     Loops     => Ctx.Current_Loops,
                     E_Loc     => Init_Item),
                  V);
               CM.Include (Union_Id (Init_Item),
                           Trivial_Connection (V));
            end;
         end loop;

         Join (FA    => FA,
               CM    => CM,
               Nodes => Verts,
               Block => Initializes_CM);
         CM.Include (Union_Id (N), Initializes_CM);
      end;

   end Do_Package_Body_Or_Stub;

   ---------------
   -- Do_Pragma --
   ---------------

   procedure Do_Pragma
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is

      function Find_Execution_Kind return Execution_Kind_T;
      --  Figures out the pragma's execution kind. For
      --  statically-false assertions we set the Execution to
      --  Abnormal_Termination.

      procedure fip;
      --  A dummy procedure called when pragma Inspection_Point is
      --  processed. This is just to help debugging Why generation. If a
      --  pragma Inspection_Point is added to a source program, then
      --  breaking on tip will get you to that point in the program.

      function Proc (N : Node_Id) return Traverse_Result;
      --  Adds N to the appropriate entry references of the current
      --  context, if N is a loop_entry reference.

      -------------------------
      -- Find_Execution_Kind --
      -------------------------

      function Find_Execution_Kind return Execution_Kind_T is
      begin
         if Get_Pragma_Id (N) /= Pragma_Check then
            return Normal_Execution;
         end if;

         declare
            PAA : constant Node_Id := First (Pragma_Argument_Associations (N));

            function Was_Assertion return Boolean;
            --  Checks if this pragma is a rewritten assert
            --  pragma.

            function Is_Statically_False return Boolean;
            --  Checks if the rewritten assertion has a
            --  statically-false argument.

            -------------------
            -- Was_Assertion --
            -------------------

            function Was_Assertion return Boolean is
              (Present (PAA)
                 and then Nkind (Expression (PAA)) = N_Identifier
                 and then Get_Name_String (Chars (Expression (PAA))) =
                            "assert");

            -------------------------
            -- Is_Statically_False --
            -------------------------

            function Is_Statically_False return Boolean is
              (Present (Next (PAA))
                 and then Nkind (Expression (Next (PAA))) =
                            N_Identifier
                 and then Entity (Expression (Next (PAA))) =
                            Standard_False);

         begin
            if Was_Assertion
              and then Is_Statically_False
            then
               return Abnormal_Termination;
            else
               return Normal_Execution;
            end if;
         end;
      end Find_Execution_Kind;

      ---------
      -- fip --
      ---------

      procedure fip is
      begin
         null;
      end fip;

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result
      is
         Loop_Name : Node_Id;
      begin
         case Nkind (N) is
            when N_Attribute_Reference =>
               case Get_Attribute_Id (Attribute_Name (N)) is
                  when Attribute_Loop_Entry =>
                     pragma Assert (Present (Ctx.Active_Loop));

                     if Present (Expressions (N)) then
                        --  This is a named loop entry reference
                        --  (i.e. X'Loop_Entry (Foo))
                        pragma Assert (List_Length (Expressions (N)) = 1);
                        Loop_Name := First (Expressions (N));
                        pragma Assert (Nkind (Loop_Name) = N_Identifier);
                        Ctx.Entry_References (Entity (Loop_Name)).Include (N);

                     else
                        Ctx.Entry_References (Ctx.Active_Loop).Include (N);
                     end if;
                  when others =>
                     null;
               end case;

            when others =>
               null;
         end case;
         return OK;
      end Proc;

      procedure Add_Loop_Entry_References is new Traverse_Proc (Proc);

      V : Flow_Graphs.Vertex_Id;
   begin
      if Pragma_Relevant_To_Flow (N) then

         case Get_Pragma_Id (N) is

            when Pragma_Unmodified   |
                 Pragma_Unreferenced =>

               --  For pragma unmodified and pragma unreferenced we
               --  produce a null vertex.
               Add_Vertex (FA, Null_Node_Attributes, V);

               declare
                  Argument_Association : Node_Id;
                  Associated_Variable  : Node_Id;
               begin
                  Argument_Association :=
                    First (Pragma_Argument_Associations (N));

                  while Present (Argument_Association) loop
                     Associated_Variable :=
                       Associated_Node (Expression (Argument_Association));

                     if not (Ekind (Associated_Variable) in
                               Subprogram_Kind)
                     then
                        if Get_Pragma_Id (N) = Pragma_Unmodified then
                           --  If a pragma Unmodified was found, we insert
                           --  its associated variable to the set of
                           --  unmodified variables.
                           FA.Unmodified_Vars.Insert (Associated_Variable);
                        else
                           --  If a pragma Unreferenced was found, we insert
                           --  its associated variable to the set of
                           --  unreferenced variables.
                           FA.Unreferenced_Vars.Insert (Associated_Variable);
                        end if;
                     end if;

                     Argument_Association := Next (Argument_Association);
                  end loop;
               end;

            when others =>
               --  If we are processing a pragma that is relevant to
               --  flow analysis, and we are not dealing with either
               --  pragma unmodified or pragma unreferenced then we
               --  create a sink vertex to check for uninitialized
               --  variables.
               Add_Vertex
                 (FA,
                  Direct_Mapping_Id (N),
                  Make_Sink_Vertex_Attributes
                    (Var_Use    => Get_Variable_Set
                       (Pragma_Argument_Associations (N),
                        Scope                => FA.B_Scope,
                        Local_Constants      => FA.Local_Constants,
                        Fold_Functions       => False,
                        Use_Computed_Globals => not FA.Compute_Globals),
                     Sub_Called => Get_Function_Set (N),
                     Is_Proof   => True,
                     E_Loc      => N,
                     Execution  => Find_Execution_Kind),
                  V);
         end case;

      else
         --  Otherwise we produce a null vertex.
         Add_Vertex (FA, Null_Node_Attributes, V);

         --  Pragma Inspection_Point is also ignored, but we insert a call
         --  to a dummy procedure, to allow to break on it during
         --  debugging.

         if Get_Pragma_Id (N) = Pragma_Inspection_Point then
            fip;
         end if;

      end if;

      CM.Include (Union_Id (N), Trivial_Connection (V));

      --  We make a note of 'Loop_Entry uses.
      case Get_Pragma_Id (N) is
         when Pragma_Check | Pragma_Loop_Variant | Pragma_Loop_Invariant =>
            Add_Loop_Entry_References (N);

         when others =>
            null;
      end case;

   end Do_Pragma;

   ---------------------
   -- Do_Precondition --
   ---------------------

   procedure Do_Precondition
     (Pre : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      pragma Unreferenced (Ctx);

      V : Flow_Graphs.Vertex_Id;
   begin
      --  We just need to check for uninitialized variables.
      Add_Vertex
        (FA,
         Direct_Mapping_Id (Pre),
         Make_Sink_Vertex_Attributes
           (Var_Use         => Get_Variable_Set
              (Pre,
               Scope                => FA.B_Scope,
               Local_Constants      => FA.Local_Constants,
               Fold_Functions       => False,
               Use_Computed_Globals => not FA.Compute_Globals),
            Sub_Called      => Get_Function_Set (Pre),
            Is_Proof        => True,
            Is_Precondition => True,
            E_Loc           => Pre),
         V);

      CM.Include (Union_Id (Pre), Trivial_Connection (V));
   end Do_Precondition;

   -----------------------------------
   --  Do_Procedure_Call_Statement  --
   -----------------------------------

   procedure Do_Procedure_Call_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      Called_Procedure : constant Entity_Id := Entity (Name (N));

      In_List  : Vertex_Vectors.Vector := Vertex_Vectors.Empty_Vector;
      Out_List : Vertex_Vectors.Vector := Vertex_Vectors.Empty_Vector;

      function Get_Abend_Kind return Execution_Kind_T;
      --  Infer how the Called_Procedure abnormally ends. If a subprogram
      --  has an output, we assume that it contains an infinite loop. If it
      --  does not, we assume its a thinly veiled wrapper around an
      --  exception raising program.
      --
      --  Certainly, if you have a procedure that never returns due to an
      --  exception, and it is implemented in SPARK, then you will run into
      --  trouble unless there is nothing of interest going on in it.
      --
      --  If we get this wrong, its not the end of the world, as failure is
      --  safe:
      --
      --  A) If the procedure throws an exception, but we think it loops
      --     forever (because it has outputs), then you might get *extra*
      --     data dependencies.
      --
      --  B) If the procedure loops forever, and:
      --     i) it has no outputs, its indistinguishable from an exception
      --     ii) it has outputs we classify it correctly
      --
      --  C) If the procedure loops forever but is not in SPARK and we have
      --     lied about contracts (as in, stated it has no outputs), then
      --     this is not a "new" failure.

      --------------------
      -- Get_Abend_Kind --
      --------------------

      function Get_Abend_Kind return Execution_Kind_T
      is
      begin
         if Out_List.Length > 0 then
            return Infinite_Loop;
         else
            return Abnormal_Termination;
         end if;
      end Get_Abend_Kind;

      V : Flow_Graphs.Vertex_Id;
      C : Flow_Graphs.Cluster_Id;

   begin
      --  Add a cluster to help pretty printing.
      FA.CFG.New_Cluster (C);

      --  A vertex for the actual call.
      Add_Vertex
        (FA,
         Direct_Mapping_Id (N),
         Make_Call_Attributes (Callsite   => N,
                               Sub_Called => Node_Sets.To_Set
                                               (Called_Procedure),
                               Loops      => Ctx.Current_Loops,
                               E_Loc      => N),
         V);
      FA.CFG.Set_Cluster (V, C);

      --  Deal with the procedures parameters.
      Process_Parameter_Associations (N,
                                      In_List,
                                      Out_List,
                                      FA, CM, Ctx);

      --  Process globals. If we generate globals we only do this if we
      --  have a user contract.
      if not FA.Compute_Globals or else
        Has_User_Supplied_Globals (Called_Procedure)
      then
         Process_Subprogram_Globals (N,
                                     In_List, Out_List,
                                     FA, CM, Ctx);
      end if;

      --  Check if we need a magic null export.
      if Has_Depends (Called_Procedure) then
         declare
            D_Map : Dependency_Maps.Map;
            V     : Flow_Graphs.Vertex_Id;
         begin
            Get_Depends (Subprogram => Called_Procedure,
                         Scope      => FA.B_Scope,
                         Depends    => D_Map);
            if D_Map.Contains (Null_Flow_Id) and then
              D_Map (Null_Flow_Id).Length >= 1
            then
               Add_Vertex
                 (FA,
                  Make_Global_Attributes
                    (Call_Vertex                  => N,
                     Global                       => Change_Variant
                       (Null_Export_Flow_Id, Out_View),
                     Discriminants_Or_Bounds_Only => False,
                     Loops                        => Ctx.Current_Loops,
                     E_Loc                        => N),
                  V);
               Out_List.Append (V);
            end if;
         end;
      end if;

      --  We now build the connection map for this sequence.
      declare
         use Vertex_Vectors;
         Combined_List : constant Vertex_Vectors.Vector :=
           Vertex_Vectors.To_Vector (V, 1) & In_List & Out_List;
         Prev          : Flow_Graphs.Vertex_Id;
      begin
         Prev := Flow_Graphs.Null_Vertex;
         for V of Combined_List loop
            if Prev /= Flow_Graphs.Null_Vertex then
               FA.CFG.Add_Edge (Prev, V, EC_Default);
            end if;
            FA.CFG.Set_Cluster (V, C);

            Prev := V;
         end loop;

         if No_Return (Called_Procedure) then
            CM.Include
              (Union_Id (N),
               Graph_Connections'
                 (Standard_Entry => V,
                  Standard_Exits => Vertex_Sets.Empty_Set));
            Linkup (FA.CFG, Prev, FA.Helper_End_Vertex);
            FA.Atr (V).Execution := Get_Abend_Kind;

            --  We note down the vertex that we just connected to the
            --  Helper_End_Vertex. If this vertex lies within dead
            --  code, then the edge will have to be removed.
            Ctx.No_Return_Vertices.Include (Prev);
         else
            CM.Include
              (Union_Id (N),
               Graph_Connections'
                 (Standard_Entry => V,
                  Standard_Exits => Vertex_Sets.To_Set (Prev)));
         end if;
      end;
   end Do_Procedure_Call_Statement;

   ----------------------
   -- Do_Postcondition --
   ----------------------

   procedure Do_Postcondition
     (Post : Node_Id;
      FA   : in out Flow_Analysis_Graphs;
      CM   : in out Connection_Maps.Map;
      Ctx  : in out Context)
   is
      pragma Unreferenced (Ctx);

      V : Flow_Graphs.Vertex_Id;
   begin
      --  We just need to check for uninitialized variables.
      Add_Vertex
        (FA,
         Direct_Mapping_Id (Post),
         Make_Sink_Vertex_Attributes
           (Var_Use          => Get_Variable_Set
              (Post,
               Scope                => FA.B_Scope,
               Local_Constants      => FA.Local_Constants,
               Fold_Functions       => False,
               Use_Computed_Globals => not FA.Compute_Globals),
            Sub_Called       => Get_Function_Set (Post),
            Is_Proof         => True,
            Is_Postcondition => True,
            E_Loc            => Post),
         V);

      CM.Include (Union_Id (Post), Trivial_Connection (V));
   end Do_Postcondition;

   ----------------------------------
   --  Do_Simple_Return_Statement  --
   ----------------------------------

   procedure Do_Simple_Return_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V : Flow_Graphs.Vertex_Id;
   begin
      if not Present (Expression (N)) then
         --  We have a return for a procedure.
         Add_Vertex (FA,
                     Direct_Mapping_Id (N),
                     Make_Aux_Vertex_Attributes (E_Loc => N),
                     V);
      else
         --  We have a function return.
         Add_Vertex
           (FA,
            Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Var_Def    => Flatten_Variable (FA.Analyzed_Entity,
                                               FA.B_Scope),
               Var_Ex_Use => Get_Variable_Set
                 (Expression (N),
                  Scope                => FA.B_Scope,
                  Local_Constants      => FA.Local_Constants,
                  Fold_Functions       => True,
                  Use_Computed_Globals => not FA.Compute_Globals),
               Sub_Called => Get_Function_Set (Expression (N)),
               Loops      => Ctx.Current_Loops,
               E_Loc      => N),
            V);
         Ctx.Folded_Function_Checks (N).Insert (Expression (N));
      end if;

      --  Control flows in, but we do not flow out again.
      CM.Include (Union_Id (N),
                  Graph_Connections'(Standard_Entry => V,
                                     Standard_Exits => Empty_Set));

      --  Instead we link this vertex directly to the helper end vertex.
      Linkup (FA.CFG, V, FA.Helper_End_Vertex);
   end Do_Simple_Return_Statement;

   ----------------------------
   -- Do_Subprogram_Or_Block --
   ----------------------------

   procedure Do_Subprogram_Or_Block
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
   begin
      if Present (Declarations (N)) then
         Process_Statement_List (Declarations (N), FA, CM, Ctx);
      end if;

      if Present (Handled_Statement_Sequence (N)) then
         Process_Statement (Handled_Statement_Sequence (N), FA, CM, Ctx);
      end if;

      if Present (Declarations (N)) and
        Present (Handled_Statement_Sequence (N))
      then
         Linkup
           (FA.CFG,
            CM (Union_Id (Declarations (N))).Standard_Exits,
            CM (Union_Id (Handled_Statement_Sequence (N))).Standard_Entry);

         CM.Include
           (Union_Id (N),
            Graph_Connections'
              (Standard_Entry => CM.Element
                 (Union_Id (Declarations (N))).Standard_Entry,
               Standard_Exits => CM.Element
                 (Union_Id (Handled_Statement_Sequence (N))).Standard_Exits));

      elsif Present (Declarations (N)) then
         CM.Include
           (Union_Id (N),
            Graph_Connections'
              (Standard_Entry => CM.Element
                 (Union_Id (Declarations (N))).Standard_Entry,
               Standard_Exits => CM.Element
                 (Union_Id (Declarations (N))).Standard_Exits));

      elsif Present (Handled_Statement_Sequence (N)) then
         CM.Include
           (Union_Id (N),
            Graph_Connections'
              (Standard_Entry => CM.Element
                 (Union_Id (Handled_Statement_Sequence (N))).Standard_Entry,
               Standard_Exits => CM.Element
                 (Union_Id (Handled_Statement_Sequence (N))).Standard_Exits));

      else
         declare
            V : Flow_Graphs.Vertex_Id;
         begin
            Add_Vertex
              (FA,
               Direct_Mapping_Id (N),
               Make_Aux_Vertex_Attributes (E_Loc => N),
               V);
            CM.Include (Union_Id (N), Trivial_Connection (V));
         end;
      end if;

   end Do_Subprogram_Or_Block;

   -------------------------
   -- Do_Type_Declaration --
   -------------------------

   procedure Do_Type_Declaration
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V   : Flow_Graphs.Vertex_Id;
      Typ : constant Node_Id := Defining_Identifier (N);
   begin
      Add_Vertex
        (FA,
         Direct_Mapping_Id (N),
         Make_Sink_Vertex_Attributes
           (Var_Use    => Get_Variable_Set
              (N,
               Scope                => FA.B_Scope,
               Local_Constants      => FA.Local_Constants,
               Fold_Functions       => False,
               Use_Computed_Globals => not FA.Compute_Globals),
            Sub_Called => Get_Function_Set (N),
            E_Loc      => N),
         V);
      CM.Include (Union_Id (N), Trivial_Connection (V));

      --  If the type has a Default_Initial_Condition then we:
      --    * add vertices for variables introduced by quantified
      --      Expressions
      --    * check if the full type is as the aspect suggested
      --      and issue a warning if not
      if Has_Default_Init_Cond (Typ)
        or else Has_Inherited_Default_Init_Cond (Typ)
      then
         if Present (Default_Init_Cond_Procedure (Typ)) then
            declare
               Expr : constant Node_Id := Get_Expr_From_Check_Only_Proc
                 (Default_Init_Cond_Procedure (Typ));
            begin
               --  Process quantified expressions
               if Present (Expr) then
                  Process_Quantified_Expressions (Expr, FA, CM, Ctx);
               end if;
            end;
         end if;

         --  Issue a warning if the declared type promised to be
         --  default initialized but is not.

         if Has_Default_Init_Cond (Typ)
           and then not Fullview_Not_In_SPARK (Typ)
           and then Is_Default_Initialized (Direct_Mapping_Id (Typ),
                                            Get_Flow_Scope (Typ))
           and then not Is_Default_Initialized (Direct_Mapping_Id (Typ),
                                                Get_Flow_Scope (Typ),
                                                Explicit_Only => True)
         then
            Error_Msg_Flow
              (FA      => FA,
               Msg     => "type & is not fully initialized",
               N       => N,
               F1      => Direct_Mapping_Id (Typ),
               Tag     => "default_initialization_missmatch",
               Kind    => Medium_Check_Kind);
         end if;
      end if;
   end Do_Type_Declaration;

   ------------------------------------
   -- Process_Quantified_Expressions --
   ------------------------------------

   procedure Process_Quantified_Expressions
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      pragma Unreferenced (CM, Ctx);

      function Proc (N : Node_Id) return Traverse_Result;
      --  Traverses the tree looking for quantified expressions. Once
      --  it finds one, it creates the 'initial and 'final vertices
      --  for the variable introduced by the quantified expression.

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Subprogram_Body        |
                 N_Subprogram_Declaration =>
               --  If we ever get one of these we skip the rest of the
               --  nodes that hang under them.
               return Skip;

            when N_Pragma =>
               if Pragma_Relevant_To_Flow (N) then
                  return OK;
               else
                  return Skip;
               end if;

            when N_Quantified_Expression =>
               if Present (Iterator_Specification (N)) then
                  Create_Initial_And_Final_Vertices
                    (Defining_Identifier (Iterator_Specification (N)),
                     False,
                     FA);
               elsif Present (Loop_Parameter_Specification (N)) then
                  Create_Initial_And_Final_Vertices
                    (Defining_Identifier (Loop_Parameter_Specification (N)),
                     False,
                     FA);
               else
                  Print_Tree_Node (N);
                  raise Why.Unexpected_Node;
               end if;

            when others =>
               null;
         end case;

         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Process => Proc);
   begin
      Traverse (N);
   end Process_Quantified_Expressions;

   procedure Process_Quantified_Expressions
     (L   : List_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      N : Node_Id := First (L);
   begin
      while Present (N) loop
         Process_Quantified_Expressions (N, FA, CM, Ctx);
         Next (N);
      end loop;
   end Process_Quantified_Expressions;

   --------------------------------
   -- Process_Subprogram_Globals --
   --------------------------------

   procedure Process_Subprogram_Globals
     (Callsite : Node_Id;
      In_List  : in out Vertex_Vectors.Vector;
      Out_List : in out Vertex_Vectors.Vector;
      FA       : in out Flow_Analysis_Graphs;
      CM       : in out Connection_Maps.Map;
      Ctx      : in out Context)
   is
      pragma Unreferenced (CM);

      Proof_Reads : Flow_Id_Sets.Set;
      Reads       : Flow_Id_Sets.Set;
      Writes      : Flow_Id_Sets.Set;
      V           : Flow_Graphs.Vertex_Id;
   begin
      --  Obtain globals (either from contracts or the computed
      --  stuff).
      Get_Globals (Subprogram   => Entity (Name (Callsite)),
                   Scope        => FA.B_Scope,
                   Proof_Ins    => Proof_Reads,
                   Reads        => Reads,
                   Writes       => Writes);
      Reads.Union (Proof_Reads);

      for R of Reads loop
         Add_Vertex (FA,
                     Make_Global_Attributes
                       (Call_Vertex                  => Callsite,
                        Global                       => R,
                        Discriminants_Or_Bounds_Only => False,
                        Loops                        => Ctx.Current_Loops,
                        E_Loc                        => Callsite),
                     V);
         In_List.Append (V);
      end loop;

      for W of Writes loop
         if not Reads.Contains (Change_Variant (W, In_View)) then
            Add_Vertex
              (FA,
               Make_Global_Attributes
                 (Call_Vertex                  => Callsite,
                  Global                       => Change_Variant (W, In_View),
                  Discriminants_Or_Bounds_Only => True,
                  Loops                        => Ctx.Current_Loops,
                  E_Loc                        => Callsite),
               V);
            In_List.Append (V);
         end if;
         Add_Vertex (FA,
                     Make_Global_Attributes
                       (Call_Vertex                  => Callsite,
                        Global                       => W,
                        Discriminants_Or_Bounds_Only => False,
                        Loops                        => Ctx.Current_Loops,
                        E_Loc                        => Callsite),
                     V);
         Out_List.Append (V);
      end loop;

   end Process_Subprogram_Globals;

   --------------------------------------
   --  Process_Parameter_Associations  --
   --------------------------------------

   procedure Process_Parameter_Associations
     (Callsite : Node_Id;
      In_List  : in out Vertex_Vectors.Vector;
      Out_List : in out Vertex_Vectors.Vector;
      FA       : in out Flow_Analysis_Graphs;
      CM       : in out Connection_Maps.Map;
      Ctx      : in out Context)
   is
      pragma Unreferenced (CM);

      Called_Subprogram : constant Entity_Id := Entity (Name (Callsite));

      P                 : Node_Id;

      V                 : Flow_Graphs.Vertex_Id;

      Actual            : Node_Id;
      Formal            : Node_Id;
      Call              : Node_Id;
   begin
      --  Create initial nodes for the statements.
      P := First (Parameter_Associations (Callsite));
      while Present (P) loop
         case Nkind (P) is
            when N_Parameter_Association =>
               --  F (A => B)
               Actual := Explicit_Actual_Parameter (P);
            when others =>
               --  F (B)
               Actual := P;
         end case;

         Find_Actual (Actual, Formal, Call);
         pragma Assert (Entity (Name (Call)) = Called_Subprogram);

         pragma Assert (Ekind (Formal) = E_In_Parameter or
                          Ekind (Formal) = E_In_Out_Parameter or
                          Ekind (Formal) = E_Out_Parameter);

         --  Build an in vertex.
         Add_Vertex
           (FA,
            Direct_Mapping_Id (P, In_View),
            Make_Parameter_Attributes
              (FA                           => FA,
               Call_Vertex                  => Callsite,
               Actual                       => Actual,
               Formal                       => Formal,
               In_Vertex                    => True,
               Discriminants_Or_Bounds_Only =>
                 Ekind (Formal) = E_Out_Parameter,
               Sub_Called                   => Get_Function_Set (Actual),
               Loops                        => Ctx.Current_Loops,
               E_Loc                        => P),
            V);
         Ctx.Folded_Function_Checks (Callsite).Insert (Actual);
         In_List.Append (V);

         --  Build an out vertex.
         if Ekind (Formal) = E_In_Out_Parameter or
           Ekind (Formal) = E_Out_Parameter
         then
            Add_Vertex
              (FA,
               Direct_Mapping_Id (P, Out_View),
               Make_Parameter_Attributes
                 (FA                           => FA,
                  Call_Vertex                  => Callsite,
                  Actual                       => Actual,
                  Formal                       => Formal,
                  In_Vertex                    => False,
                  Discriminants_Or_Bounds_Only => False,
                  Loops                        => Ctx.Current_Loops,
                  E_Loc                        => P),
               V);
            Out_List.Append (V);
         end if;
         --  Go to the next statement
         P    := Next (P);
      end loop;
   end Process_Parameter_Associations;

   ------------------------------
   --  Process_Statement_List  --
   ------------------------------

   procedure Process_Statement_List
     (L   : List_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      P              : Node_Or_Entity_Id;
      Statement_List : Union_Lists.List := Union_Lists.Empty_List;
      Block          : Graph_Connections;
   begin
      --  Create initial nodes for the statements.
      P := First (L);
      while Present (P) loop
         case Nkind (P) is
            when N_Freeze_Entity                |
              N_Freeze_Generic_Entity           |
              N_Generic_Instantiation           |
              N_Generic_Package_Declaration     |
              N_Generic_Subprogram_Declaration  |
              N_Implicit_Label_Declaration      |
              N_Incomplete_Type_Declaration     |
              N_Itype_Reference                 |
              N_Label                           |
              N_Number_Declaration              |
              N_Object_Renaming_Declaration     |
              N_Package_Renaming_Declaration    |
              N_Private_Type_Declaration        |
              N_Representation_Clause           |
              N_Subprogram_Body                 |
              N_Subprogram_Body_Stub            |
              N_Subprogram_Declaration          |
              N_Subprogram_Renaming_Declaration |
              N_Use_Package_Clause              |
              N_Use_Type_Clause                 |
              N_Validate_Unchecked_Conversion   =>
               --  We completely skip these.
               null;

            when others =>
               Process_Statement (P, FA, CM, Ctx);
               Statement_List.Append (Union_Id (P));

         end case;
         P := Next (P);
      end loop;

      --  Produce the joined up list.
      Join (FA    => FA,
            CM    => CM,
            Nodes => Statement_List,
            Block => Block);
      CM.Include (Union_Id (L), Block);

   end Process_Statement_List;

   -------------------------
   --  Process_Statement  --
   -------------------------

   procedure Process_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      L : Vertex_Vectors.Vector := Vertex_Vectors.Empty_Vector;
   begin

      --  Initialize the set of expressions we need to double check.
      Ctx.Folded_Function_Checks.Insert (N, Node_Sets.Empty_Set);

      --  Deal with the statement.
      case Nkind (N) is
         when N_Assignment_Statement =>
            Do_Assignment_Statement (N, FA, CM, Ctx);
         when N_Block_Statement =>
            Do_Subprogram_Or_Block (N, FA, CM, Ctx);
         when N_Case_Statement =>
            Do_Case_Statement (N, FA, CM, Ctx);
         when N_Exit_Statement =>
            Do_Exit_Statement (N, FA, CM, Ctx);
         when N_Extended_Return_Statement =>
            Do_Extended_Return_Statement (N, FA, CM, Ctx);
         when N_Handled_Sequence_Of_Statements =>
            Do_Handled_Sequence_Of_Statements (N, FA, CM, Ctx);
         when N_If_Statement =>
            Do_If_Statement (N, FA, CM, Ctx);
         when N_Loop_Statement =>
            Do_Loop_Statement (N, FA, CM, Ctx);
         when N_Null_Statement =>
            Do_Null_Or_Raise_Statement (N, FA, CM, Ctx);
         when N_Object_Declaration =>
            Do_Object_Declaration (N, FA, CM, Ctx);
         when N_Package_Declaration =>
            Do_Package_Declaration (N, FA, CM, Ctx);
         when N_Package_Body | N_Package_Body_Stub =>
            Do_Package_Body_Or_Stub (N, FA, CM, Ctx);
         when N_Pragma =>
            Do_Pragma (N, FA, CM, Ctx);
         when N_Procedure_Call_Statement =>
            --  Check for aliasing first
            if not FA.Compute_Globals then
               --  ??? We will get errors during flow analysis - to be
               --  investigated if there are issues here if we produce
               --  useless contracts?
               Check_Procedure_Call (N, FA.Aliasing_Present);
            end if;

            --  Then process the procedure call
            Do_Procedure_Call_Statement (N, FA, CM, Ctx);
         when N_Simple_Return_Statement =>
            Do_Simple_Return_Statement (N, FA, CM, Ctx);
         when N_Full_Type_Declaration | N_Subtype_Declaration =>
            Do_Type_Declaration (N, FA, CM, Ctx);
         when N_Raise_Statement |
              N_Raise_xxx_Error =>
            Do_Null_Or_Raise_Statement (N, FA, CM, Ctx);
         when others =>
            Print_Node_Subtree (N);
            --  ??? To be added by various future tickets. Eventually
            --  we will replace this with a Why.Unexpected_Node
            --  exception.
            raise Why.Not_Implemented;
      end case;

      --  We chain the folded function checks in front of the actual vertex
      --  for this statement, if necessary. First we create a vertex for
      --  each expression we need to check.

      for Expr of Ctx.Folded_Function_Checks (N) loop
         declare
            Unchecked : constant Flow_Id_Sets.Set :=
              Get_Variable_Set
              (Expr,
               Scope                => FA.B_Scope,
               Local_Constants      => FA.Local_Constants,
               Fold_Functions       => False,
               Use_Computed_Globals => not FA.Compute_Globals) -

              Get_Variable_Set
              (Expr,
               Scope                => FA.B_Scope,
               Local_Constants      => FA.Local_Constants,
               Fold_Functions       => True,
               Use_Computed_Globals => not FA.Compute_Globals);
            V : Flow_Graphs.Vertex_Id;
         begin
            if Unchecked.Length > 0 then
               Add_Vertex
                 (FA,
                  Make_Sink_Vertex_Attributes (Var_Use       => Unchecked,
                                               Is_Fold_Check => True,
                                               E_Loc         => Expr),
                  V);
               L.Append (V);
            end if;
         end;
      end loop;

      --  Then, if we created any new vertices we need to link them in
      --  front of the vertex created for N. We then re-adjust the standard
      --  entry for N.

      if L.Length >= 1 then
         L.Append (CM (Union_Id (N)).Standard_Entry);

         declare
            Prev : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
         begin
            for V of L loop
               if Prev /= Flow_Graphs.Null_Vertex then
                  Linkup (FA.CFG, Prev, V);
               end if;
               Prev := V;
            end loop;
         end;

         CM (Union_Id (N)).Standard_Entry := L.First_Element;
      end if;

      --  Finally, we remove the set, so we can do a final sanity check to
      --  make sure all of these have been processed. This sanity check is
      --  in the postcondition of Process_Statement and again at the end of
      --  Create.

      Ctx.Folded_Function_Checks.Delete (N);
   end Process_Statement;

   ----------------------
   -- RHS_Split_Useful --
   ----------------------

   function RHS_Split_Useful (N     : Node_Id;
                              Scope : Flow_Scope)
                              return Boolean is

      function Rec (N : Node_Id) return Boolean;
      --  Recursive helper function.

      function Rec (N : Node_Id) return Boolean is
      begin
         if Ekind (Get_Full_Type (N, Scope)) not in Record_Kind
         then
            --  No point in trying to split if we are not dealing with some
            --  record type.
            return False;
         end if;

         case Nkind (N) is
            when N_Identifier | N_Expanded_Name | N_Aggregate =>
               return True;

            when N_Selected_Component =>
               return Rec (Prefix (N));

            when N_Attribute_Reference =>
               return Get_Attribute_Id (Attribute_Name (N)) = Attribute_Update
                 and then Rec (Prefix (N));

            when N_Qualified_Expression | N_Type_Conversion =>
               return Rec (Expression (N));

            when others =>
               return False;
         end case;
      end Rec;

   begin
      return Rec (Expression (N));
   end RHS_Split_Useful;

   -----------------------------
   -- Prune_Exceptional_Paths --
   -----------------------------

   procedure Prune_Exceptional_Paths (FA : in out Flow_Analysis_Graphs) is
      procedure Prune (V   : Flow_Graphs.Vertex_Id;
                       Ins : out Flow_Graphs.Simple_Traversal_Instruction);
      --  Helper subprogram for DFS traversal. This traversal sets the
      --  Is_Null_Node flag of dead vertices.

      function Is_Dead (V : Flow_Graphs.Vertex_Id) return Boolean;
      --  Check if the given vertex cannot reach the end vertex on
      --  normal execution or if the given vertex cannot be reached
      --  from the start vertex on normal execution.

      function Dead_Path_Exists
        (From : Flow_Graphs.Vertex_Id;
         To   : Flow_Graphs.Vertex_Id)
         return Boolean;
      --  Check if there exists a path between vertices From and To
      --  that crosses a vertex which has an execution mode of either
      --  Abnormal_Termination or an Infinite_Loop.

      -------------
      -- Is_Dead --
      -------------

      function Is_Dead (V : Flow_Graphs.Vertex_Id) return Boolean is
         Dead_Going_Down : Boolean := True;
         Dead_Going_Up   : Boolean := True;
         Reversed        : Boolean;

         procedure Test (V   : Flow_Graphs.Vertex_Id;
                         Ins : out Flow_Graphs.Simple_Traversal_Instruction);
         --  Helper subprogram for DFS traversal.

         ----------
         -- Test --
         ----------

         procedure Test (V   : Flow_Graphs.Vertex_Id;
                         Ins : out Flow_Graphs.Simple_Traversal_Instruction)
         is
            V_Check : constant Flow_Graphs.Vertex_Id :=
              (if Reversed
               then FA.Start_Vertex
               else FA.Helper_End_Vertex);
         begin
            if V = V_Check then
               if Reversed then
                  Dead_Going_Up := False;
               else
                  Dead_Going_Down := False;
               end if;
               Ins := Flow_Graphs.Abort_Traversal;

            elsif FA.Atr (V).Execution = Abnormal_Termination then
               Ins := Flow_Graphs.Skip_Children;

            elsif FA.Atr (V).Execution = Infinite_Loop then
               declare
                  F : constant Flow_Id := FA.CFG.Get_Key (V);
               begin
                  if F.Kind = Direct_Mapping
                    and then Nkind (Get_Direct_Mapping_Id (F)) =
                               N_Procedure_Call_Statement
                  then
                     Ins := Flow_Graphs.Skip_Children;
                  else
                     Ins := Flow_Graphs.Continue;
                  end if;
               end;

            else
               Ins := Flow_Graphs.Continue;
            end if;
         end Test;

      begin
         Reversed := False;
         FA.CFG.DFS (Start         => V,
                     Include_Start => True,
                     Visitor       => Test'Access,
                     Reversed      => Reversed);
         Reversed := True;
         FA.CFG.DFS (Start         => V,
                     Include_Start => True,
                     Visitor       => Test'Access,
                     Reversed      => Reversed);
         return Dead_Going_Up or Dead_Going_Down;
      end Is_Dead;

      -----------
      -- Prune --
      -----------

      procedure Prune (V   : Flow_Graphs.Vertex_Id;
                       Ins : out Flow_Graphs.Simple_Traversal_Instruction)
      is
      begin
         if V = FA.Helper_End_Vertex then
            Ins := Flow_Graphs.Skip_Children;
         else
            Ins := Flow_Graphs.Continue;
            if Is_Dead (V) then
               FA.Atr (V).Is_Null_Node := True;
            end if;
         end if;
      end Prune;

      ----------------------
      -- Dead_Path_Exists --
      ----------------------

      function Dead_Path_Exists
        (From : Flow_Graphs.Vertex_Id;
         To   : Flow_Graphs.Vertex_Id)
         return Boolean
      is
         Found_Dead_Path : Boolean := False;

         procedure Test (V   : Flow_Graphs.Vertex_Id;
                         Ins : out Flow_Graphs.Simple_Traversal_Instruction);
         --  Helper subprogram for DFS traversal.

         ----------
         -- Test --
         ----------

         procedure Test (V   : Flow_Graphs.Vertex_Id;
                         Ins : out Flow_Graphs.Simple_Traversal_Instruction)
         is
         begin
            if V = To then
               Ins := Flow_Graphs.Skip_Children;
            elsif FA.Atr (V).Execution in Abnormal_Termination |
                                          Infinite_Loop
            then
               if FA.CFG.Non_Trivial_Path_Exists (V, To) then
                  Found_Dead_Path := True;
                  Ins := Flow_Graphs.Abort_Traversal;
               else
                  Ins := Flow_Graphs.Continue;
               end if;
            else
               Ins := Flow_Graphs.Continue;
            end if;
         end Test;

      begin
         FA.CFG.DFS (Start         => From,
                     Include_Start => False,
                     Visitor       => Test'Access);
         return Found_Dead_Path;
      end Dead_Path_Exists;

   begin
      FA.CFG.DFS (Start         => FA.Start_Vertex,
                  Include_Start => False,
                  Visitor       => Prune'Access);

      --  Populate the Edges_To_Remove field of FA.
      for From of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         for To of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
            if From /= To
              and then not Is_Dead (From)
              and then not Is_Dead (To)
              and then not FA.CFG.Edge_Exists (From, To)
              and then Dead_Path_Exists (From, To)
            then
               declare
                  VD : constant Vertex_Pair := (From => From,
                                                To   => To);
               begin
                  FA.Edges_To_Remove.Include (VD);
               end;
            end if;
         end loop;
      end loop;

   end Prune_Exceptional_Paths;

   ------------------
   -- Simplify_CFG --
   ------------------

   procedure Simplify_CFG (FA : in out Flow_Analysis_Graphs) is
   begin
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         if FA.Atr (V).Is_Null_Node then
            --  Close the subgraph indicated by V's neighbours.
            for A of FA.CFG.Get_Collection (V, Flow_Graphs.In_Neighbours) loop
               for B of FA.CFG.Get_Collection (V,
                                               Flow_Graphs.Out_Neighbours)
               loop
                  declare
                     VD : constant Vertex_Pair := (From => A,
                                                   To   => B);
                  begin
                     if not FA.Edges_To_Remove.Contains (VD) then
                        FA.CFG.Add_Edge (A, B, EC_Default);
                     end if;
                  end;
               end loop;
            end loop;

            --  Remove all edges from the vertex.
            FA.CFG.Clear_Vertex (V);

            --  Clear the node.
            FA.Atr (V) := Null_Attributes'Update (Is_Null_Node => True);
         end if;
      end loop;
   end Simplify_CFG;

   -----------------------------
   -- Pragma_Relevant_To_Flow --
   -----------------------------

   function Pragma_Relevant_To_Flow (N : Node_Id) return Boolean is
   begin
      case Get_Pragma_Id (N) is
         when Pragma_Check =>
            return not Is_Ignored_Pragma_Check (N);

         when Pragma_Loop_Variant =>
            return True;

         when Pragma_Unmodified   |
              Pragma_Unreferenced =>
            return True;

         --  Do not issue a warning on invariant pragmas, as one is already
         --  issued on the corresponding type in SPARK.Definition.

         when Pragma_Invariant
            | Pragma_Type_Invariant
            | Pragma_Type_Invariant_Class =>
            return False;

         --  Do not issue a warning on unknown pragmas, as one is already
         --  issued in SPARK.Definition.

         when Unknown_Pragma =>
            return False;

         --  Remaining pragmas fall into two major groups:
         --
         --  Group 1 - ignored
         --
         --  Pragmas that do not need any marking, either because:
         --  . they are defined by SPARK 2014, or
         --  . they are already taken into account elsewhere (contracts)
         --  . they have no effect on flow analysis

         --  Group 1a - RM Table 16.1, Ada language-defined pragmas marked
         --  "Yes".
         --  Note: pragma Assert is transformed into an
         --  instance of pragma Check by the front-end.
         when Pragma_Assertion_Policy             |
              Pragma_Atomic                       |
              Pragma_Atomic_Components            |
              Pragma_Convention                   |
              Pragma_Elaborate                    |
              Pragma_Elaborate_All                |
              Pragma_Elaborate_Body               |
              Pragma_Export                       |
              Pragma_Import                       |
              Pragma_Independent                  |
              Pragma_Independent_Components       |
              Pragma_Inline                       |
              Pragma_Linker_Options               |
              Pragma_List                         |
              Pragma_No_Return                    |
              Pragma_Normalize_Scalars            |
              Pragma_Optimize                     |
              Pragma_Pack                         |
              Pragma_Page                         |
              Pragma_Partition_Elaboration_Policy |
              Pragma_Preelaborable_Initialization |
              Pragma_Preelaborate                 |
              Pragma_Profile                      |
              Pragma_Pure                         |
              Pragma_Restrictions                 |
              Pragma_Reviewable                   |
              Pragma_Suppress                     |
              Pragma_Unsuppress                   |
              Pragma_Volatile                     |
              Pragma_Volatile_Components          |

         --  Group 1b - RM Table 16.2, SPARK language-defined pragmas marked
         --  "Yes", whose effect on flow analysis is taken care of somewhere
         --  else.
         --  Note: pragmas Assert_And_Cut, Assume, and
         --  Loop_Invariant are transformed into instances of
         --  pragma Check by the front-end.
              Pragma_Abstract_State               |
              Pragma_Assume_No_Invalid_Values     |
              Pragma_Async_Readers                |
              Pragma_Async_Writers                |
              Pragma_Contract_Cases               |
              Pragma_Depends                      |
              Pragma_Default_Initial_Condition    |
              Pragma_Effective_Reads              |
              Pragma_Effective_Writes             |
              Pragma_Global                       |
              Pragma_Initializes                  |
              Pragma_Initial_Condition            |
              Pragma_Overflow_Mode                |
              Pragma_Part_Of                      |
              Pragma_Postcondition                |
              Pragma_Precondition                 |
              Pragma_Refined_Depends              |
              Pragma_Refined_Global               |
              Pragma_Refined_Post                 |
              Pragma_Refined_State                |
              Pragma_SPARK_Mode                   |
              Pragma_Unevaluated_Use_Of_Old       |

         --  Group 1c - RM Table 16.3, GNAT implementation-defined pragmas
         --  marked "Yes".
         --  Note: pragma Debug is removed by the front-end.
              Pragma_Ada_83                       |
              Pragma_Ada_95                       |
              Pragma_Ada_05                       |
              Pragma_Ada_2005                     |
              Pragma_Ada_12                       |
              Pragma_Ada_2012                     |
              Pragma_Annotate                     |
              Pragma_Check_Policy                 |
              Pragma_Inline_Always                |
              Pragma_Inspection_Point             |
              Pragma_Linker_Section               |
              Pragma_No_Elaboration_Code_All      |
              Pragma_No_Tagged_Streams            |
              Pragma_Pure_Function                |
              Pragma_Restriction_Warnings         |
              Pragma_Style_Checks                 |
              Pragma_Test_Case                    |
              Pragma_Validity_Checks              |
              Pragma_Warnings                     |
              Pragma_Weak_External                =>
            return False;

         --  Group 1d - pragma that are re-written and/or removed
         --  by the front-end in GNATProve, so they should
         --  never be seen here.
         when Pragma_Assert                       |
              Pragma_Assert_And_Cut               |
              Pragma_Assume                       |
              Pragma_Debug                        |
              Pragma_Loop_Invariant               =>
            raise Program_Error;

         --  Group 2 - Remaining pragmas, enumerated here rather than
         --  a "when others" to force re-consideration when
         --  SNames.Pragma_Id is extended.
         --
         --  These all generate a warning.  In future, these pragmas
         --  may move to be fully ignored or to be processed with more
         --  semantic detail as required.

         --  Group 2a - GNAT Defined and obsolete pragmas
         when Pragma_Abort_Defer                 |
           Pragma_Allow_Integer_Address          |
           Pragma_Attribute_Definition           |
           Pragma_C_Pass_By_Copy                 |
           Pragma_Check_Float_Overflow           |
           Pragma_Check_Name                     |
           Pragma_CIL_Constructor                |
           Pragma_Comment                        |
           Pragma_Common_Object                  |
           Pragma_Compile_Time_Error             |
           Pragma_Compile_Time_Warning           |
           Pragma_Compiler_Unit                  |
           Pragma_Compiler_Unit_Warning          |
           Pragma_Complete_Representation        |
           Pragma_Complex_Representation         |
           Pragma_Component_Alignment            |
           Pragma_Controlled                     |
           Pragma_Convention_Identifier          |
           Pragma_CPP_Class                      |
           Pragma_CPP_Constructor                |
           Pragma_CPP_Virtual                    |
           Pragma_CPP_Vtable                     |
           Pragma_CPU                            |
           Pragma_Debug_Policy                   |
           Pragma_Default_Scalar_Storage_Order   |
           Pragma_Default_Storage_Pool           |
           Pragma_Detect_Blocking                |
           Pragma_Disable_Atomic_Synchronization |
           Pragma_Dispatching_Domain             |
           Pragma_Elaboration_Checks             |
           Pragma_Eliminate                      |
           Pragma_Enable_Atomic_Synchronization  |
           Pragma_Export_Function                |
           Pragma_Export_Object                  |
           Pragma_Export_Procedure               |
           Pragma_Export_Value                   |
           Pragma_Export_Valued_Procedure        |
           Pragma_Extend_System                  |
           Pragma_Extensions_Allowed             |
           Pragma_External                       |
           Pragma_External_Name_Casing           |
           Pragma_Fast_Math                      |
           Pragma_Favor_Top_Level                |
           Pragma_Finalize_Storage_Only          |
           Pragma_Ident                          |
           Pragma_Implementation_Defined         |
           Pragma_Implemented                    |
           Pragma_Implicit_Packing               |
           Pragma_Import_Function                |
           Pragma_Import_Object                  |
           Pragma_Import_Procedure               |
           Pragma_Import_Valued_Procedure        |
           Pragma_Initialize_Scalars             |
           Pragma_Inline_Generic                 |
           Pragma_Interface                      |
           Pragma_Interface_Name                 |
           Pragma_Interrupt_Handler              |
           Pragma_Interrupt_State                |
           Pragma_Java_Constructor               |
           Pragma_Java_Interface                 |
           Pragma_Keep_Names                     |
           Pragma_License                        |
           Pragma_Link_With                      |
           Pragma_Linker_Alias                   |
           Pragma_Linker_Constructor             |
           Pragma_Linker_Destructor              |
           Pragma_Loop_Optimize                  |
           Pragma_Machine_Attribute              |
           Pragma_Main                           |
           Pragma_Main_Storage                   |
           Pragma_Memory_Size                    |
           Pragma_No_Body                        |
           Pragma_No_Inline                      |
           Pragma_No_Run_Time                    |
           Pragma_No_Strict_Aliasing             |
           Pragma_Obsolescent                    |
           Pragma_Optimize_Alignment             |
           Pragma_Ordered                        |
           Pragma_Overriding_Renamings           |
           Pragma_Passive                        |
           Pragma_Persistent_BSS                 |
           Pragma_Polling                        |
           Pragma_Post                           |
           Pragma_Post_Class                     |
           Pragma_Pre                            |
           Pragma_Predicate                      |
           Pragma_Prefix_Exception_Messages      |
           Pragma_Pre_Class                      |
           Pragma_Priority_Specific_Dispatching  |
           Pragma_Profile_Warnings               |
           Pragma_Propagate_Exceptions           |
           Pragma_Provide_Shift_Operators        |
           Pragma_Psect_Object                   |
           Pragma_Rational                       |
           Pragma_Ravenscar                      |
           Pragma_Relative_Deadline              |
           Pragma_Remote_Access_Type             |
           Pragma_Restricted_Run_Time            |
           Pragma_Share_Generic                  |
           Pragma_Shared                         |
           Pragma_Short_Circuit_And_Or           |
           Pragma_Short_Descriptors              |
           Pragma_Simple_Storage_Pool_Type       |
           Pragma_Source_File_Name               |
           Pragma_Source_File_Name_Project       |
           Pragma_Source_Reference               |
           Pragma_Static_Elaboration_Desired     |
           Pragma_Storage_Unit                   |
           Pragma_Stream_Convert                 |
           Pragma_Subtitle                       |
           Pragma_Suppress_All                   |
           Pragma_Suppress_Debug_Info            |
           Pragma_Suppress_Exception_Locations   |
           Pragma_Suppress_Initialization        |
           Pragma_System_Name                    |
           Pragma_Task_Info                      |
           Pragma_Task_Name                      |
           Pragma_Task_Storage                   |
           Pragma_Thread_Local_Storage           |
           Pragma_Time_Slice                     |
           Pragma_Title                          |
           Pragma_Unchecked_Union                |
           Pragma_Unimplemented_Unit             |
           Pragma_Universal_Aliasing             |
           Pragma_Universal_Data                 |
           Pragma_Unreferenced_Objects           |
           Pragma_Unreserve_All_Interrupts       |
           Pragma_Use_VADS_Size                  |
           Pragma_Warning_As_Error               |
           Pragma_Wide_Character_Encoding        |

           --  Group 2b - Ada RM pragmas
           Pragma_Discard_Names                  |
           Pragma_Locking_Policy                 |
           Pragma_Queuing_Policy                 |
           Pragma_Task_Dispatching_Policy        |
           Pragma_All_Calls_Remote               |
           Pragma_Asynchronous                   |
           Pragma_Attach_Handler                 |
           Pragma_Remote_Call_Interface          |
           Pragma_Remote_Types                   |
           Pragma_Shared_Passive                 |
           Pragma_Interrupt_Priority             |
           Pragma_Lock_Free                      |
           Pragma_Priority                       |
           Pragma_Storage_Size                   =>

            Errout.Error_Msg_Name_1 := Pragma_Name (N);
            Errout.Error_Msg_N
              ("?pragma % ignored in flow analysis (not yet supported)", N);
            return False;

         --  ??? ignored for now, see NA03-003

         when Pragma_Extensions_Visible =>
            return False;
      end case;

   end Pragma_Relevant_To_Flow;

   ------------------------------------------------------------
   --  Package functions and procedures
   ------------------------------------------------------------

   -------------
   -- Create --
   -------------

   procedure Create (FA : in out Flow_Analysis_Graphs)
   is
      Connection_Map  : Connection_Maps.Map := Connection_Maps.Empty_Map;
      The_Context     : Context             := No_Context;
      Subprogram_Spec : Entity_Id;
      Preconditions   : Node_Lists.List;
      Precon_Block    : Graph_Connections;
      Postcon_Block   : Graph_Connections;
      Body_N          : Node_Id;
      Spec_N          : Node_Id;
      Package_Writes  : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      pragma Assert (Is_Valid (FA));

      case FA.Kind is
         when E_Subprogram_Body =>
            Body_N        :=
              SPARK_Util.Get_Subprogram_Body (FA.Analyzed_Entity);
            Preconditions := Get_Precondition_Expressions (FA.Analyzed_Entity);

            if Acts_As_Spec (Body_N) then
               Subprogram_Spec := Defining_Unit_Name (Specification (Body_N));
            else
               Subprogram_Spec := Corresponding_Spec (Body_N);
            end if;

         when E_Package =>
            Spec_N := Get_Enclosing (FA.Analyzed_Entity,
                                     N_Package_Specification);
            Body_N := Spec_N;

         when E_Package_Body =>
            Body_N := Get_Enclosing (FA.Analyzed_Entity,
                                     N_Package_Body);
            Spec_N := Get_Enclosing (Corresponding_Spec (Body_N),
                                     N_Package_Specification);

      end case;

      --  Create the magic start, helper end and end vertices.
      declare
         Start_Atr : V_Attributes := Null_Attributes;
      begin
         --  We attach the subprogram's location to the start vertex
         --  as it gives us a convenient way to generate error
         --  messages applying to the whole subprogram/package/body.
         Start_Atr.Error_Location := Body_N;
         Add_Vertex (FA, Start_Atr, FA.Start_Vertex);
      end;
      Add_Vertex (FA, Null_Attributes, FA.Helper_End_Vertex);
      Add_Vertex (FA, Null_Attributes, FA.End_Vertex);

      --  Create the magic null export vertices.
      declare
         F : constant Flow_Id := Change_Variant (Null_Export_Flow_Id,
                                                 Initial_Value);
      begin
         Add_Vertex (FA, F, Make_Null_Export_Attributes (F));
      end;
      declare
         F : constant Flow_Id := Change_Variant (Null_Export_Flow_Id,
                                                 Final_Value);
      begin
         Add_Vertex (FA, F, Make_Null_Export_Attributes (F));
      end;

      --  Collect parameters of the analyzed entity and produce
      --  initial and final vertices.
      case FA.Kind is
         when E_Subprogram_Body =>
            declare
               E : Entity_Id;
            begin
               E := First_Formal (Subprogram_Spec);
               while Present (E) loop
                  Create_Initial_And_Final_Vertices (E, True, FA);
                  E := Next_Formal (E);
               end loop;
            end;

         when E_Package | E_Package_Body =>
            --  No parameters to see here.
            null;
      end case;

      --  Collect globals for the analyzed entity and create initial
      --  and final vertices.
      case FA.Kind is
         when E_Subprogram_Body =>
            if not FA.Compute_Globals then
               declare
                  type G_Prop is record
                     Is_Read     : Boolean;
                     Is_Write    : Boolean;
                     Is_Proof_In : Boolean;
                  end record;

                  package Global_Maps is new Ada.Containers.Hashed_Maps
                    (Key_Type        => Flow_Id,
                     Element_Type    => G_Prop,
                     Hash            => Hash,
                     Equivalent_Keys => "=",
                     "="             => "=");

                  Proof_Ins : Flow_Id_Sets.Set;
                  Reads     : Flow_Id_Sets.Set;
                  Writes    : Flow_Id_Sets.Set;
                  Globals   : Global_Maps.Map := Global_Maps.Empty_Map;
               begin
                  Get_Globals (Subprogram => Subprogram_Spec,
                               Scope      => FA.B_Scope,
                               Proof_Ins  => Proof_Ins,
                               Reads      => Reads,
                               Writes     => Writes);
                  for G of Proof_Ins loop
                     Globals.Include (Change_Variant (G, Normal_Use),
                                      G_Prop'(Is_Read     => False,
                                              Is_Write    => False,
                                              Is_Proof_In => True));
                  end loop;
                  for G of Reads loop
                     Globals.Include (Change_Variant (G, Normal_Use),
                                      G_Prop'(Is_Read     => True,
                                              Is_Write    => False,
                                              Is_Proof_In => False));
                  end loop;
                  for G of Writes loop
                     declare
                        P : G_Prop;
                     begin
                        if Globals.Contains (Change_Variant (G, Normal_Use))
                        then
                           P := Globals (Change_Variant (G, Normal_Use));
                           P.Is_Write := True;
                        else
                           P := G_Prop'(Is_Read     => False,
                                        Is_Write    => True,
                                        Is_Proof_In => False);
                        end if;
                        Globals.Include (Change_Variant (G, Normal_Use), P);

                        --  If we are dealing with a function, since we found a
                        --  global output, we raise an error.
                        if Ekind (FA.Analyzed_Entity) = E_Function then
                           Error_Msg_Flow
                             (FA   => FA,
                              Msg  => "function with output global & " &
                                "is not allowed in SPARK",
                              N    => FA.Analyzed_Entity,
                              F1   => G,
                              Kind => Error_Kind,
                              Tag  => "side_effects");

                           FA.Function_Side_Effects_Present := True;
                        end if;
                     end;
                  end loop;

                  for C in Globals.Iterate loop
                     declare
                        G : constant Flow_Id := Global_Maps.Key (C);
                        P : constant G_Prop  := Global_Maps.Element (C);

                        Mode : Param_Mode;
                     begin
                        if P.Is_Read and P.Is_Write then
                           Mode := Mode_In_Out;
                        elsif P.Is_Read then
                           Mode := Mode_In;
                        elsif P.Is_Write then
                           Mode := Mode_Out;
                        elsif P.Is_Proof_In then
                           Mode := Mode_Proof;
                        else
                           raise Program_Error;
                        end if;

                        Create_Initial_And_Final_Vertices (G, Mode, False, FA);
                     end;
                  end loop;
               end;
            end if;

         when E_Package | E_Package_Body =>
            --  Packages have no obvious globals, but we can extract a
            --  list of global variables used from the optional rhs of
            --  the initializes clause:
            --
            --     Initializes => (State => (Global_A, ...),
            --
            --  Any other use of non-local variables is not legal (SRM
            --  7.1.5, verification rule 12).
            --
            --  Any such globals are global inputs *only* as packages
            --  are only allowed to initialize their own state.
            declare
               Global_Ins : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
               --  We need to make sure to only add each global once
               --  (an entity might be used to derive more than one of
               --  our states).

               The_Out : Flow_Id;
               The_In  : Flow_Id_Sets.Set;
               DM      : Dependency_Maps.Map;
            begin
               if Present (FA.Initializes_N) then
                  DM := Parse_Initializes (FA.Initializes_N);
                  for C in DM.Iterate loop
                     The_Out := Dependency_Maps.Key (C);
                     The_In  := Dependency_Maps.Element (C);

                     for G of The_In loop
                        if not Global_Ins.Contains (G) then
                           Global_Ins.Include (G);
                           Create_Initial_And_Final_Vertices
                             (F             => G,
                              Mode          => Mode_In,
                              Uninitialized => False,
                              FA            => FA);
                        end if;
                     end loop;

                     if Present (The_Out) then
                        Package_Writes.Include (The_Out);
                     end if;
                  end loop;
               end if;
            end;

            --  If a Refined_State aspect exists, we gather all
            --  constituents that are abstract states and create
            --  Initial and Final vertices for them.

            if FA.Kind = E_Package_Body then
               declare
                  Refined_State_N : constant Node_Id :=
                    Get_Pragma (FA.Analyzed_Entity,
                                Pragma_Refined_State);

                  Constituents    : Flow_Id_Sets.Set;
                  DM              : Dependency_Maps.Map;
               begin
                  if Present (Refined_State_N) then
                     DM := Parse_Initializes (Refined_State_N);
                     for C in DM.Iterate loop
                        Constituents := Dependency_Maps.Element (C);

                        for Constituent of Constituents loop
                           if Is_Abstract_State (Constituent) then
                              --  Found a constituent that is an
                              --  abstract state. We now create
                              --  Initial and Final vertices for it.

                              Create_Initial_And_Final_Vertices
                                (F             => Constituent,
                                 Mode          =>
                                   (if Is_Initialized_At_Elaboration
                                         (Constituent,
                                          FA.B_Scope)
                                    then Mode_In_Out
                                    else Mode_In),
                                 Uninitialized =>
                                   not Is_Initialized_At_Elaboration
                                         (Constituent,
                                          FA.B_Scope),
                                 FA            => FA);
                           end if;
                        end loop;
                     end loop;
                  end if;
               end;
            end if;

      end case;

      --  Collect variables introduced by quantified expressions. We
      --  need to look at the following parts:
      --     - precondition
      --     - postcondition
      --     - initial_condition
      --     - declarative part
      --     - body
      case FA.Kind is
         when E_Subprogram_Body =>
            for Precondition of Preconditions loop
               Process_Quantified_Expressions
                 (Precondition, FA, Connection_Map, The_Context);
            end loop;
            for Refined in Boolean loop
               declare
                  Postconditions : Node_Lists.List :=
                    Get_Postcondition_Expressions (FA.Analyzed_Entity,
                                                   Refined);
               begin
                  for Postcondition of Postconditions loop
                     Process_Quantified_Expressions
                       (Postcondition, FA, Connection_Map, The_Context);
                  end loop;
               end;
            end loop;
            Process_Quantified_Expressions
              (Declarations (Body_N), FA, Connection_Map, The_Context);
            Process_Quantified_Expressions
              (Statements (Handled_Statement_Sequence (Body_N)),
               FA, Connection_Map, The_Context);

         when E_Package =>
            Process_Quantified_Expressions
              (Visible_Declarations (Spec_N), FA, Connection_Map, The_Context);
            Process_Quantified_Expressions
              (Private_Declarations (Spec_N), FA, Connection_Map, The_Context);
            --  Look into initial conditions
            declare
               Postconditions : Node_Lists.List :=
                 Get_Postcondition_Expressions (FA.Analyzed_Entity,
                                                False);
            begin
               for Postcondition of Postconditions loop
                  Process_Quantified_Expressions
                    (Postcondition, FA, Connection_Map, The_Context);
               end loop;
            end;

         when E_Package_Body =>
            --  Look into the spec
            Process_Quantified_Expressions
              (Visible_Declarations (Spec_N), FA, Connection_Map, The_Context);
            Process_Quantified_Expressions
              (Private_Declarations (Spec_N), FA, Connection_Map, The_Context);

            --  Look at the body
            Process_Quantified_Expressions
              (Declarations (Body_N), FA, Connection_Map, The_Context);
            if Present (Handled_Statement_Sequence (Body_N)) then
               Process_Quantified_Expressions
                 (Statements (Handled_Statement_Sequence (Body_N)),
                  FA, Connection_Map, The_Context);
            end if;

            --  Look into initial conditions
            declare
               Postconditions : Node_Lists.List :=
                 Get_Postcondition_Expressions (Spec_Entity
                                                  (FA.Analyzed_Entity),
                                                False);
            begin
               for Postcondition of Postconditions loop
                  Process_Quantified_Expressions
                    (Postcondition, FA, Connection_Map, The_Context);
               end loop;
            end;

      end case;

      --  If we are dealing with a function, we use its entity to deal
      --  with the value returned.
      if Ekind (FA.Analyzed_Entity) = E_Function then
         Create_Initial_And_Final_Vertices (FA.Analyzed_Entity, False, FA);
      end if;

      --  If you're now wondering where we deal with locally declared
      --  objects; we deal with them as they are encountered. See
      --  Do_Object_Declaration for enlightenment.

      --  Produce flowgraph for the precondition and postcondition if
      --  any.
      case FA.Kind is
         when E_Subprogram_Body =>
            --  Flowgraph for preconditions and left hand sides of
            --  contract cases.
            declare
               NL : Union_Lists.List := Union_Lists.Empty_List;
            begin
               for Precondition of Preconditions loop
                  Do_Precondition (Precondition,
                                   FA,
                                   Connection_Map,
                                   The_Context);
                  NL.Append (Union_Id (Precondition));
               end loop;
               Join (FA    => FA,
                     CM    => Connection_Map,
                     Nodes => NL,
                     Block => Precon_Block);
            end;

            --  Flowgraph for postconditions and right hand sides of
            --  contract cases.
            declare
               NL             : Union_Lists.List := Union_Lists.Empty_List;
               Postconditions : Node_Lists.List;
            begin
               for Refined in Boolean loop
                  Postconditions := Get_Postcondition_Expressions
                    (FA.Analyzed_Entity,
                     Refined);

                  for Postcondition of Postconditions loop
                     Do_Postcondition (Postcondition,
                                       FA,
                                       Connection_Map,
                                       The_Context);
                     NL.Append (Union_Id (Postcondition));
                  end loop;
               end loop;
               Join (FA    => FA,
                     CM    => Connection_Map,
                     Nodes => NL,
                     Block => Postcon_Block);
            end;

         when E_Package | E_Package_Body =>
            --  Flowgraph for initial_condition aspect
            declare
               Spec_E         : constant Entity_Id :=
                 (if Ekind (FA.Analyzed_Entity) = E_Package
                  then FA.Analyzed_Entity
                  else Spec_Entity (FA.Analyzed_Entity));
               NL             : Union_Lists.List := Union_Lists.Empty_List;
               Postconditions : constant Node_Lists.List :=
                 Get_Postcondition_Expressions (Spec_E,
                                                False);
            begin
               for Postcondition of Postconditions loop
                  Do_Postcondition (Postcondition,
                                    FA,
                                    Connection_Map,
                                    The_Context);
                  NL.Append (Union_Id (Postcondition));
               end loop;
               Join (FA    => FA,
                     CM    => Connection_Map,
                     Nodes => NL,
                     Block => Postcon_Block);
            end;

      end case;

      --  Produce flowgraphs for the body and link to start, helper
      --  end and end vertex.
      case FA.Kind is
         when E_Subprogram_Body =>
            Do_Subprogram_Or_Block (Body_N, FA, Connection_Map, The_Context);

            --  Connect up all the dots...
            Linkup (FA.CFG,
                    FA.Start_Vertex,
                    Precon_Block.Standard_Entry);
            Linkup (FA.CFG,
                    Precon_Block.Standard_Exits,
                    Connection_Map (Union_Id (Body_N)).Standard_Entry);
            Linkup (FA.CFG,
                    Connection_Map (Union_Id (Body_N)).Standard_Exits,
                    FA.Helper_End_Vertex);
            Linkup (FA.CFG,
                    FA.Helper_End_Vertex,
                    Postcon_Block.Standard_Entry);
            Linkup (FA.CFG,
                    Postcon_Block.Standard_Exits,
                    FA.End_Vertex);

         when E_Package | E_Package_Body =>
            declare
               UL   : Union_Lists.List := Union_Lists.Empty_List;
               Prev : Union_Id;
            begin
               if Present (Visible_Declarations (Spec_N)) then
                  Process_Statement_List (Visible_Declarations (Spec_N),
                                          FA, Connection_Map, The_Context);

                  UL.Append (Union_Id (Visible_Declarations (Spec_N)));
               end if;

               --  Ok, we need a copy of all variables from the spec +
               --  initializes. Although this is somewhat
               --  out-of-place, this is the only place we can
               --  assemble them easily without re-doing a lot of the
               --  hard work we've done so far.
               FA.Visible_Vars := FA.All_Vars or Package_Writes;

               if Present (Private_Declarations (Spec_N)) then
                  Process_Statement_List (Private_Declarations (Spec_N),
                                          FA, Connection_Map, The_Context);
                  UL.Append (Union_Id (Private_Declarations (Spec_N)));
               end if;

               if FA.Kind = E_Package_Body then
                  Do_Subprogram_Or_Block (Body_N,
                                          FA, Connection_Map, The_Context);
                  UL.Append (Union_Id (Body_N));
               end if;

               Prev := Union_Id (Empty);
               Linkup (FA.CFG,
                       FA.Start_Vertex,
                       Connection_Map (UL.First_Element).Standard_Entry);
               for X of UL loop
                  if Prev /= Union_Id (Empty) then
                     Linkup (FA.CFG,
                             Connection_Map (Prev).Standard_Exits,
                             Connection_Map (X).Standard_Entry);
                  end if;
                  Prev := X;
               end loop;
               Linkup (FA.CFG,
                       Connection_Map (UL.Last_Element).Standard_Exits,
                       FA.Helper_End_Vertex);
               Linkup (FA.CFG,
                       FA.Helper_End_Vertex,
                       Postcon_Block.Standard_Entry);
               Linkup (FA.CFG,
                       Postcon_Block.Standard_Exits,
                       FA.End_Vertex);

            end;
      end case;

      --  Remove edges between non-returning subprograms which are
      --  within dead code and the Helper_End_Vertex.
      for V of The_Context.No_Return_Vertices loop
         if not Flow_Graphs.Non_Trivial_Path_Exists (FA.CFG,
                                                     FA.Start_Vertex,
                                                     V)
         then
            Flow_Graphs.Remove_Edge (FA.CFG,
                                     V,
                                     FA.Helper_End_Vertex);
         end if;
      end loop;

      --  Remove:
      --    *  all vertices that inevitably lead to a raise statement,
      --       a statically-false assertion or a non-returning procedure
      --    *  all vertices that follow a raise statement, a
      --       statically-false assertion or a non-returning procedure
      --       that are not otherwise reachable from the start vertex
      Prune_Exceptional_Paths (FA);

      --  Simplify graph by removing all null vertices.
      Simplify_CFG (FA);

      --  Assemble the set of directly called subprograms.
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         FA.Direct_Calls.Union (FA.Atr (V).Subprograms_Called);
      end loop;

      --  In GG mode, we assemble a list of globals and subprograms
      --  now (and retroactively make some initial and final
      --  vertices).
      if FA.Compute_Globals then
         declare
            Known_Vars : constant Flow_Id_Sets.Set :=
              To_Entire_Variables (FA.All_Vars);
         begin
            for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
               declare
                  Atr  : constant V_Attributes     := FA.Atr (V);
                  Vars : constant Flow_Id_Sets.Set :=
                    To_Entire_Variables (Atr.Variables_Used or
                                           Atr.Variables_Defined);
               begin
                  for Var of Vars loop
                     if not Synthetic (Var) and then
                       not Known_Vars.Contains (Var)
                     then
                        FA.GG.Globals.Include (Get_Direct_Mapping_Id (Var));
                     end if;
                  end loop;
               end;
            end loop;
         end;

         for E of FA.GG.Globals loop
            case Ekind (E) is
               when E_In_Parameter | E_Constant =>
                  Create_Initial_And_Final_Vertices (Direct_Mapping_Id (E),
                                                     Mode_In, False, FA);
               when others =>
                  Create_Initial_And_Final_Vertices (Direct_Mapping_Id (E),
                                                     Mode_In_Out, False, FA);
            end case;
         end loop;

         for E of FA.Direct_Calls loop
            declare
               F : constant Flow_Id := Direct_Mapping_Id (E);
               V : Flow_Graphs.Vertex_Id;
               A : V_Attributes;
            begin
               if FA.CFG.Get_Vertex (Change_Variant (F, Initial_Value)) =
                 Flow_Graphs.Null_Vertex
               then
                  --  If the 'Initial and 'Final vertices do not
                  --  already exist then we create them.

                  --  Setup the n'initial vertex.
                  A := Make_Variable_Attributes (F_Ent => Change_Variant
                                                   (F, Initial_Value),
                                                 Mode  => Mode_In_Out,
                                                 E_Loc => E);

                  Add_Vertex
                    (FA,
                     Change_Variant (F, Initial_Value),
                     A,
                     V);
                  Linkup (FA.CFG, V, FA.Start_Vertex);

                  Create_Record_Tree (Change_Variant (F, Initial_Value),
                                      A,
                                      FA);

                  --  Setup the n'final vertex.
                  Add_Vertex
                    (FA,
                     Change_Variant (F, Final_Value),
                     Make_Variable_Attributes (F_Ent => Change_Variant
                                                 (F, Final_Value),
                                               Mode  => Mode_In_Out,
                                               E_Loc => E),
                     V);
                  Linkup (FA.CFG, FA.End_Vertex, V);
               end if;
            end;
         end loop;
      end if;

      --  Note if this is a subprogram with no effects.
      if FA.Kind = E_Subprogram_Body then
         FA.No_Effects := True;
         for F of FA.All_Vars loop
            declare
               V : constant Flow_Graphs.Vertex_Id :=
                 FA.CFG.Get_Vertex (Change_Variant (F, Final_Value));
            begin
               pragma Assert (V /= Flow_Graphs.Null_Vertex);
               if FA.Atr.Element (V).Is_Export then
                  FA.No_Effects := False;
                  exit;
               end if;
            end;
         end loop;
      end if;

      --  Finally, we need to make sure that all extra checks for folded
      --  functions have been processed.
      pragma Assert (The_Context.Folded_Function_Checks.Length = 0);
   end Create;

end Flow.Control_Flow_Graph;
