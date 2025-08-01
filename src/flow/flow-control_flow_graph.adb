------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              F L O W . C O N T R O L _ F L O W _ G R A P H               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2013-2025, Capgemini Engineering              --
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

with Atree;       use Atree;
with Elists;      use Elists;
with Exp_Util;
with Lib;         use Lib;
with Namet;       use Namet;
with Nlists;      use Nlists;
with Rtsfind;     use Rtsfind;
with Sem_Aux;     use Sem_Aux;
with Sem_Eval;    use Sem_Eval;
with Sem_Type;    use Sem_Type;
with Sem_Util;    use Sem_Util;
with Sinfo.Nodes; use Sinfo.Nodes;
with Sinfo.Utils; use Sinfo.Utils;
with Snames;      use Snames;
with Stand;       use Stand;
with Treepr;      use Treepr;
with Uintp;       use Uintp;

with Common_Iterators;       use Common_Iterators;
with Hashing;                use Hashing;
with SPARK_Definition;       use SPARK_Definition;
with SPARK_Util;             use SPARK_Util;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with SPARK_Util.Types;       use SPARK_Util.Types;

with Errout_Wrapper;                  use Errout_Wrapper;
with Flow_Classwide;                  use Flow_Classwide;
with Flow.Control_Flow_Graph.Utility; use Flow.Control_Flow_Graph.Utility;
with Flow_Debug;                      use Flow_Debug;
with Flow_Error_Messages;             use Flow_Error_Messages;
with Flow_Generated_Globals;          use Flow_Generated_Globals;
with Flow_Generated_Globals.Phase_1;  use Flow_Generated_Globals.Phase_1;
with Flow_Refinement;                 use Flow_Refinement;
with Flow_Utility.Initialization;     use Flow_Utility.Initialization;
with Flow_Utility.Proof_Dependencies; use Flow_Utility.Proof_Dependencies;
with Flow_Utility;                    use Flow_Utility;

with VC_Kinds; use VC_Kinds;
with Why;

pragma Unreferenced (Flow_Debug);

--  Documentation on how we deal with some non-obvious constructs.
--
--  Note: This is a new section and thus somewhat incomplete, but the idea
--  is to document any new, non-obvious decisions here.
--
--  Dynamic_Predicate
--  =================
--  The front-end translates this into a special function which is then
--  implicitly called. We need to check two things: we do not use variables
--  in the predicate, and explicit membership should have the constants
--  with variable inputs used in the predicate appear.
--
--  We currently ignore any proof-flow for the dynamic predicate; and the
--  membership effects are introduced as follows:
--  * only in phase 1, Get_Functions will add calls to the predicates for
--    membership tests
--  * in phase 1, we generate normal globals for the predicate functions
--  * in phase 2, we add the global effects of predicates in Get_Variables for
--    membership tests
--  * in phase 2 sanity checking, we examine the global variables of the
--    predicate functions
--
--  Type Invariants and DIC
--  =======================
--  These two aspects are translated by the fron-end into procedures inside a
--  freeze block and do not appear in the tree for GNATprove. We do create a
--  sink vertex for them at an object declaration in order to detect calls and
--  variables used in their expressions.

package body Flow.Control_Flow_Graph is

   use type Ada.Containers.Count_Type;

   use type Flow_Graphs.Vertex_Id;

   use Vertex_Sets;
   use type Flow_Id_Sets.Set;

   package Union_Lists is new
     Ada.Containers.Doubly_Linked_Lists (Element_Type => Union_Id, "=" => "=");

   ------------------------------------------------------------
   --  Local types
   ------------------------------------------------------------

   subtype Nodes_Ignored_By_Process_Statement is Node_Kind
   with
     Static_Predicate =>
       Nodes_Ignored_By_Process_Statement
       in N_Abstract_Subprogram_Declaration
        | N_Call_Marker
        | N_Freeze_Entity
        | N_Freeze_Generic_Entity
        | N_Generic_Instantiation
        | N_Generic_Package_Declaration
        | N_Generic_Renaming_Declaration
        | N_Generic_Subprogram_Declaration
        | N_Implicit_Label_Declaration
        | N_Incomplete_Type_Declaration
        | N_Itype_Reference
        | N_Number_Declaration
        | N_Object_Renaming_Declaration
        | N_Package_Renaming_Declaration
        | N_Private_Type_Declaration
        | N_Protected_Body
        | N_Protected_Body_Stub
        | N_Protected_Type_Declaration
        | N_Representation_Clause
        | N_Subprogram_Body
        | N_Subprogram_Body_Stub
        | N_Subprogram_Declaration
        | N_Subprogram_Renaming_Declaration
        | N_Task_Body
        | N_Task_Body_Stub
        | N_Task_Type_Declaration
        | N_Use_Package_Clause
        | N_Use_Type_Clause
        | N_Validate_Unchecked_Conversion
        | N_Variable_Reference_Marker;

   package Vertex_Lists is new
     Ada.Containers.Doubly_Linked_Lists
       (Element_Type => Flow_Graphs.Vertex_Id);

   ---------------------
   -- Connection_Maps --
   ---------------------

   --  The flow graph is produced using two data structures,
   --  Graph_Connections and a map Union_Id -> Graph_Connections.
   --
   --  Any node in the AST may be represented by some vertices in the
   --  flow graph. For example, if N is a N_Subprogram_Body and its
   --  Handled_Statement_Sequence contains the following statement:
   --
   --     if X > 0 then
   --        X := X - 1;
   --     else
   --        X := 0;
   --     end if;
   --
   --  Lets start at the bottom. We recurse down the tree and at some point we
   --  will call Do_Assignment_Statement for each of the two assignments. Every
   --  Do_FOOBAR procedure takes a FOOBAR node, and fills in the connection map
   --  for that node.
   --
   --  So, for the first assignment statement (assume this node is Ass_1 in
   --  the AST) we create a vertex (but no edges!) in the flow graph. We also
   --  create an entry in the connection map from Ass_1 to a connection map
   --  with the trivial "unit" connection.
   --
   --        GRAPH            CM
   --    0. [X := X - 1]      Ass_1 -> (0, {0})
   --
   --  (Where "0." is the vertex id of the node for "X := X - 1".) Each
   --  connection map captures a single entry vertex (0 in our example) and a
   --  set of exit vertices ({0} in our example). Read this as "control flow
   --  for the node Ass_1 is as follows: control goes into this vertex (0), we
   --  do one thing, and control leaves this vertex (0)".
   --
   --  Lets process the second assignment statement, our graph and connection
   --  map now looks like this:
   --
   --        GRAPH            CM
   --    0. [X := X - 1]      Ass_1 -> (0, {0})
   --    1. [X := 0]          Ass_2 -> (1, {1})
   --
   --  We now go up the tree and look at Do_If_Statement. First we produce a
   --  vertex (it will be number "2") in the graph for the N_If_Statement
   --  itself. We then assemble the connection map as follows:
   --
   --     - The entry point for the if statement is obviously the if statement
   --       itself (i.e. 2).
   --
   --     - We have two ways we can exit from the if statement S: we can fall
   --       off the end of the then branch (Then_Statements (S)) or of the else
   --       branch (Else_Statements (S)). So the exits of the if statement
   --       are the union of all exits of all branches.
   --
   --  To determine the exit of one of our branch we simply look into the
   --  connection map for what is recorded for Then_Statements (S) and
   --  Else_Statements (S). Here we get Ass_1 and Ass_2, but in general you'd
   --  get some kind of List_Id.
   --
   --  So now our picture looks like this:
   --
   --        GRAPH            CM
   --    0. [X := X - 1]      Ass_1 -> (0, {0})
   --    1. [X := 0]          Ass_2 -> (1, {1})
   --    2. [if X > 0]        S     -> (2, {0, 1})
   --
   --  But wait, we still have not added any edges to the flow graph. We need
   --  to make sure that we have edges from vertex 2 to the Then_Statements (S)
   --  and to the Else_Statements (S). The Do_If_Statement procedure will also
   --  call one of the Linkup procedures. These take two argumens:
   --  a group of "from" points and a single "to" point, and create edges
   --  from all "from" to the "to".
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
   --  Note that only the graph was changed by Linkup and not the connection
   --  map. The connection map for node N can be considered to be a "summary
   --  for node N and all child nodes".

   type Graph_Connections is record
      Standard_Entry : Flow_Graphs.Vertex_Id;
      Standard_Exits : Vertex_Sets.Set;
   end record;

   No_Connections : constant Graph_Connections :=
     Graph_Connections'
       (Standard_Entry => Flow_Graphs.Null_Vertex,
        Standard_Exits => Vertex_Sets.Empty_Set);

   function Trivial_Connection
     (V : Flow_Graphs.Vertex_Id) return Graph_Connections
   is (Graph_Connections'
         (Standard_Entry => V, Standard_Exits => Vertex_Sets.To_Set (V)))
   with Pre => V /= Flow_Graphs.Null_Vertex;
   --  Produce the trivial connection

   function Union_Hash (X : Union_Id) return Ada.Containers.Hash_Type
   is (Generic_Integer_Hash (Integer (X)));

   package Connection_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Union_Id,
        Element_Type    => Graph_Connections,
        Hash            => Union_Hash,
        Equivalent_Keys => "=",
        "="             => "=");

   procedure Move_Connections
     (CM : in out Connection_Maps.Map; Dst : Union_Id; Src : Union_Id)
   with
     Pre  => CM.Contains (Src) and not CM.Contains (Dst),
     Post => CM.Contains (Dst) and not CM.Contains (Src);
   --  Create the connection map for Dst and moves all fields from Src to it

   procedure fndi (E : Entity_Id; N : Node_Id);
   --  This is a debug procedure that is called whenever we add a vertex N to
   --  the graph for entity E. The name is "flow node debug info". It is here
   --  so we can break on it in the debugger.

   ----------
   -- fndi --
   ----------

   procedure fndi (E : Entity_Id; N : Node_Id) is
      pragma Unreferenced (E);
      pragma Unreferenced (N);
   begin
      null;
   end fndi;

   -------------
   -- Context --
   -------------

   --  The context is a bag of extra state that is passed around through each
   --  Do_* procedure.
   --
   --  Perhaps the most important aspect of the Context is the
   --  Folded_Function_Checks stack, which is used to keep track of functions
   --  with dependency relations. The only reason to put a dependency relation
   --  on a function is to note that not all parameters have been used.
   --  For example:
   --
   --     function Multiply_After_Delay (A, B : Integer;
   --                                    W    : Float)
   --                                    return Integer
   --     with Depends => (Multiply_After_Delay'Result => (A, B),
   --                      null                        => W);
   --
   --  If such a function is used, we do not want W to flow into the final
   --  result of whatever it is doing, however, this is difficult as functions
   --  are not really processed separately. Instead we are just interested in
   --  the "set of variables" present in an expression. So instead we have a
   --  parameter in Get_Variables (Fold_Functions) which, if specified, will
   --  return simply the set {A, B} instead of {A, B, W} for expressions
   --  involving calls to Multiply_After_Delay.
   --
   --  However, we need to make sure that all variables are initialized when we
   --  call our function; but the generated vertex for an expression involving
   --  it no longer features W.
   --
   --  Hence, in all places where we call Get_Variables and fold functions, we
   --  also remember the node_id of the expression. For example, if we have an
   --  if statement:
   --
   --     if Multiply_After_Delay (X, Y, Z) = 0 then
   --        ...
   --
   --  Lets assume the node_id for the statement is 42, and the node_id for
   --  Condition (42) is 88. When we process Get_Variables (88), we place the
   --  following into the Folded_Function_Checks map:
   --
   --     42 -> {88}
   --
   --  At the end of Process_Statement we then re-check each of these
   --  expression and emit a sink vertex in front of the original vertex
   --  to check only the "unused" variables.
   --
   --  Inspect the graphs generated for test M412-008 for more information.
   --
   --  Finally we take a note of all vertices that are linked directly to the
   --  Helper_End_Vertex because they belong to a non-returning procedure.
   --  Vertices of this kind that lie within dead code will have to be
   --  unlinked at the end.

   package Borrowers_Markers is new
     Ada.Containers.Doubly_Linked_Lists (Ada.Containers.Count_Type);
   --  To keep track of how many local borrowers exist when entering a loop, so
   --  that we know how many of them need to be reclaimed by an EXIT statement.
   --
   --  Note: it would be much easier to keep track of cursors on the
   --  stack of borrowers. However, this stack grows/shrinks as borrowers
   --  appear/disappear and this would be tampering with cursors, should
   --  cursors exist. Instead, we record the number of elements in the stack.

   package Goto_Jump_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Entity_Id,
        Element_Type    => Vertex_Sets.Set,
        Hash            => Node_Hash,
        Equivalent_Keys => "=");
   --  Maps from labels entities (e.g. "<<L1>>") to vertices with their
   --  matching goto statements (e.g. "goto L1").

   type Context is record
      Vertex_Ctx : Vertex_Context;
      --  Context that will be passed to vertex attributes

      Active_Loop : Entity_Id;
      --  The currently processed loop. This is always a member of
      --  Current_Loops, unless no loop is currently processed.

      Termination_Proved : Boolean;
      --  Set to True iff the current loop has been proven to terminate

      Entry_References : Node_Graphs.Map;
      --  A map from loops -> 'Loop_Entry references

      Folded_Function_Checks : Node_Lists.List;
      --  Nodes we need to separately check for uninitialized variables due to
      --  function folding.

      Borrowers : Node_Lists.List;
      --  Stack of object declarations for local borrowers

      Borrow_Numbers : Borrowers_Markers.List;
      --  Numbers of local borrowers in scope at each sequence_of_statements

      Goto_Jumps : Goto_Jump_Maps.Map;
      --  Map for connecting gotos with labels

      Extended_Return : Opt_N_Extended_Return_Statement_Id;
      --  The extended return statement
   end record;

   No_Context : constant Context :=
     Context'
       (Vertex_Ctx             => No_Vertex_Context,
        Active_Loop            => Types.Empty,
        Termination_Proved     => False,
        Entry_References       => Node_Graphs.Empty_Map,
        Folded_Function_Checks => Node_Lists.Empty_List,
        Borrowers              => Node_Lists.Empty_List,
        Borrow_Numbers         => Borrowers_Markers.Empty_List,
        Goto_Jumps             => Goto_Jump_Maps.Empty_Map,
        Extended_Return        => Types.Empty);

   ------------------------------------------------------------
   --  Local declarations
   ------------------------------------------------------------

   procedure Add_Dummy_Vertex
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map);
   --  Adds a null CFG vertex for node N with trivial connections

   procedure Add_Vertex
     (FA : in out Flow_Analysis_Graphs; F : Flow_Id; A : V_Attributes);
   --  Helper procedure to add a vertex (with attributes) to the graph

   procedure Add_Vertex
     (FA : in out Flow_Analysis_Graphs;
      F  : Flow_Id;
      A  : V_Attributes;
      V  : out Flow_Graphs.Vertex_Id);
   --  Helper procedure to add a vertex (with attributes) to the graph,
   --  returning the Id of the newly added vertex.

   procedure Add_Vertex
     (FA : in out Flow_Analysis_Graphs;
      A  : V_Attributes;
      V  : out Flow_Graphs.Vertex_Id);
   --  Helper procedure to add an unkeyed vertex (with attributes) to the
   --  graph, returning its Id.

   procedure Linkup
     (FA    : in out Flow_Analysis_Graphs;
      Froms : Vertex_Sets.Set;
      To    : Flow_Graphs.Vertex_Id)
   with Pre => To /= Flow_Graphs.Null_Vertex;
   --  Link all vertices in Froms to the To vertex in the given graph

   procedure Linkup
     (FA   : in out Flow_Analysis_Graphs;
      From : Flow_Graphs.Vertex_Id;
      To   : Flow_Graphs.Vertex_Id)
   with
     Pre =>
       From /= Flow_Graphs.Null_Vertex and then To /= Flow_Graphs.Null_Vertex;
   --  Link the From to the To vertex in the given graph

   procedure Join
     (FA    : in out Flow_Analysis_Graphs;
      CM    : in out Connection_Maps.Map;
      Nodes : Union_Lists.List;
      Block : out Graph_Connections)
   with
     Pre  => (for all Node of Nodes => CM.Contains (Node)),
     Post =>
       CM.Length = CM.Length'Old - Nodes.Length
       and then (for all Node of Nodes => not CM.Contains (Node));
   --  Join up the standard entry and standard exits of the given nodes.
   --  Block contains the combined standard entry and exits of the joined
   --  up sequence. Entries for the nodes are removed from the connection map.

   procedure Clear_Vertex_And_Attributes
     (FA : in out Flow_Analysis_Graphs; V : Flow_Graphs.Vertex_Id);
   --  Clear vertex V, its attributes and set Is_Null_Node to True. The values
   --  of Is_Original_Program_Node and Error_Location in the attributes are
   --  kept because they are read in a routine that detects dead code.

   procedure Create_Record_Tree
     (F : Flow_Id; Leaf_Atr : V_Attributes; FA : in out Flow_Analysis_Graphs)
   with Pre => F.Kind in Direct_Mapping | Record_Field | Magic_String;
   --  Create part of the tree structure used to represent records. In
   --  particular, we create the subtree which is formed by the leaf F up to
   --  the entire variable represented by F. In the art below the vertices
   --  marked with a * are created by this procedure if F is R.A.Y. If we
   --  come to a vertex which already exists, we stop. This means calling this
   --  procedure once for each leaf will eventually result in the entire tree.
   --
   --                  R*
   --                 / \
   --                /   \
   --             R.A*    R.B
   --            /   \
   --           /     \
   --      R.A.X       R.A.Y*

   procedure Create_Initial_And_Final_Vertices
     (E : Entity_Id; FA : in out Flow_Analysis_Graphs)
   with
     Pre =>
       Ekind (E)
       in E_Abstract_State
        | E_Loop_Parameter
        | E_Variable
        | E_Constant
        | E_Function
        | Formal_Kind
        | E_Protected_Type
        | E_Task_Type;
   --  Create the 'initial and 'final vertices for the given entity and link
   --  them up to the start and end vertices.

   procedure Create_Initial_And_Final_Vertices
     (F : Flow_Id; Mode : Param_Mode; FA : in out Flow_Analysis_Graphs)
   with
     Pre =>
       F.Kind in Direct_Mapping | Magic_String and then F.Variant = Normal_Use;
   --  Create the 'initial and 'final vertices for the given global and link
   --  them up to the start and end vertices.

   procedure Do_Assignment_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Pre => Nkind (N) = N_Assignment_Statement;
   --  Process assignment statements. Pretty obvious stuff

   procedure Do_Call_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Pre => Nkind (N) in N_Subprogram_Call | N_Entry_Call_Statement;
   --  Deal with procedure and entry calls. We follow the ideas of the SDG
   --  paper by Horowitz, Reps and Binkley and have a separate vertex for
   --  each parameter (if a paramater is an in out, we have two vertices
   --  modelling it).
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
   --  Globals are treated like parameters.
   --
   --  For entries (procedures, functions and entries in protected types)
   --  we also have the protected object as an implicit volatile input
   --  and/or output.
   --
   --  Each of these vertices will also have Call_Vertex set in its
   --  attributes so that we can fiddle the CDG to look like this:
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
   --
   --  For calls to subprograms that might raise an exception, e.g.:
   --
   --     procedure P (A              : in  Integer;
   --                  By_Copy        : out Integer;
   --                  By_Reference   : out <limited record type>;
   --                  By_Unspecified : out <record type>)
   --     with Exceptional_Cases => ...;
   --
   --  when we produce a more complicated CFG:
   --
   --     call P
   --     |
   --     a_in := x
   --     |
   --     by_reference_out   := ...
   --     |
   --     <raise> ---## EXCEPTION RAISED ##----- <havoc>
   --     |                                VD := {by_unspecified}
   --     ## NORMAL TERMINATION ##               /  |  \
   --     |                                     /   |   \
   --     by_copy_out        := ...            /    |    \
   --     |                                   /     |     \
   --     by_unspecified_out := ...          /      |      \
   --     |                                 /       |       \
   --     {standard exit}                  /        |        \
   --                                     /         |         \
   --                               [reclaim1] [reclaim2] ... [reclaim all]
   --                               |          |              |
   --                               [handler1] [handler2] ... [exceptional_end]
   --
   --  i.e. parameters passed by reference (and globals) are written regardless
   --  of exception being raised; parameters passed by copy are only written
   --  when the callee terminates normally; parameters whose passing mode is
   --  unspecified are written when the subprogram terminates normally and
   --  unintialized when it raises an exception.

   procedure Do_Case_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Pre => Nkind (N) = N_Case_Statement;
   --  The CFG that we generate for case statements looks like
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

   procedure Do_Continue_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Pre => Nkind (N) = N_Continue_Statement;
   --  Deal with continue statements in loops. We treat them as goto, storing
   --  the continue vertex in the set associated to the loop entity in
   --  Ctx.Goto_Jumps.

   procedure Do_Contract_Expression
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Pre => Nkind (N) in N_Subexpr;
   --  Deals with the given pre- or postcondition expression

   procedure Do_Delay_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Pre => Nkind (N) in N_Delay_Statement;
   --  Deal with delay until X statements. We make a vertex where we use all
   --  variables from the expression and we also implicitly use
   --  Ada.Real_Time.Clock_Time.

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
   with
     Pre  =>
       Nkind (N) = N_Extended_Return_Statement
       and then not Ctx.Vertex_Ctx.In_Nested_Package
       and then No (Ctx.Extended_Return),
     Post => No (Ctx.Extended_Return);
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

   procedure Do_Goto_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Pre => Nkind (N) = N_Goto_Statement;
   --  Deal with forward goto statements. For each goto statement we create
   --  a vertex. In the connection map it will be its own standard entry (as
   --  usual), but will have no standard exits (because forward gotos jump to
   --  labels that we have seen yet). Instead, we record this vertex in the
   --  context paramter Ctx and we will connect it with the vertex for the
   --  label in Do_Label.

   procedure Do_Handled_Sequence_Of_Statements
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Pre => Nkind (N) = N_Handled_Sequence_Of_Statements;
   --  Deals with handled sequence of statements, possibly with exception
   --  handlers. We generate a CFG which looks like this:
   --
   --  stmt1
   --  |
   --  stmt2
   --  |
   --  stmt...
   --  |
   --  |         [handler1]   [handler2]   [hander...]
   --  |         |            |            |
   --
   --  i.e. there might be multiple standard exits coming from the normal
   --  execution and the exception handlers.

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

   procedure Do_Label
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Pre => Nkind (N) = N_Label;
   --  Deal with goto labels; see Do_Goto_Statement

   procedure Do_Loop_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with
     Pre  => Nkind (N) = N_Loop_Statement and then Present (Identifier (N)),
     Post =>
       Ctx.Vertex_Ctx.Current_Loops.Length
       = Ctx.Vertex_Ctx.Current_Loops'Old.Length;
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

   procedure Do_Null_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with
     Pre =>
       Nkind (N)
       in N_Null_Statement
        | N_Exception_Declaration
        | N_Exception_Renaming_Declaration
       or else (Nkind (N) = N_Block_Statement
                and then Nkind (Original_Node (N)) in N_Subprogram_Call);
   --  Deals with null statements. We create a new vertex that has control flow
   --  in from the top and leave from the bottom (nothing happens in between).
   --  Exception declarations are treated like null statements and subprogram
   --  calls inlined into block statements too.

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
   --  This procedure ignores objects that are part of single
   --  concurrent types.

   procedure Do_Package_Body_Or_Stub
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Pre => Nkind (N) in N_Package_Body | N_Package_Body_Stub;
   --  When we find a nested package body, we bring its initializes clause
   --  to bear.
   --
   --  Lets remind ourselves of the example from Do_Package_Declaration:
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
   --  Finally, we look into the nested package body when the package declares
   --  no state abstractions. This is similar to what we do for the package
   --  spec. Note that we only process the declarations of the package's body
   --  and we only do so if the package's body is actually in SPARK.

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
   --    3) If the nested package has an initializes aspect then the private
   --       part is ignored. However, if there is no initializes aspect and
   --       if the private part is in SPARK then it is processed.
   --
   --  Note that the initializes aspect is *not* considered yet, as it only
   --  holds once the package body has been elaborated. See
   --  Do_Package_Body_Or_Stub below for more information.

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

   procedure Do_Raise_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Pre => Nkind (N) = N_Raise_Statement;
   --  Deals with explicit raise statements

   procedure Do_Raise_xxx_Error
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Pre => Nkind (N) in N_Raise_xxx_Error;
   --  Deals with implicit raise statements

   procedure Do_Simple_Return_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with
     Pre =>
       Nkind (N) = N_Simple_Return_Statement
       and then not Ctx.Vertex_Ctx.In_Nested_Package;
   --  This deals with return statements (with and without an
   --  expression). They do not have a standard exit, instead we
   --  directly link them to the end vertex.

   procedure Do_Subprogram_Or_Block
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with
     Pre =>
       Nkind (N)
       in N_Subprogram_Body
        | N_Task_Body
        | N_Block_Statement
        | N_Package_Body
        | N_Entry_Body;
   --  This is the top level procedure which deals with a subprogram,
   --  block or package elaboration statement. The declarations and
   --  sequence of statements is processed and linked.
   --
   --  If we are given an entry body, we also have to deal with the
   --  barrier. We do this by adding a node for the condition with two
   --  paths, one leading to the subprogram and one non-traversable path
   --  (EC_Barrier) skipping it; this is to introduce a control dependence
   --  on the barrier:
   --
   --                      |
   --                 when BARRIER
   --                /            \
   --  (EC_Default) /              \ (EC_Barrier)
   --              /                \
   --          SUBPROGRAM          null
   --                    \         /
   --                     \---+---/
   --                         |

   procedure Do_Type_Declaration
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with
     Pre =>
       Nkind (N)
       in N_Full_Type_Declaration
        | N_Subtype_Declaration
        | N_Private_Extension_Declaration;
   --  This ignores type declarations (but creates a sink vertex so we
   --  can check for use of uninitialized variables).

   procedure Process_Call_Actuals
     (Callsite            : Node_Id;
      Ins                 : in out Vertex_Lists.List;
      Outs_By_Copy        : in out Vertex_Lists.List;
      Outs_By_Reference   : in out Vertex_Lists.List;
      Outs_By_Unspecified : in out Vertex_Lists.List;
      FA                  : in out Flow_Analysis_Graphs;
      CM                  : in out Connection_Maps.Map;
      Ctx                 : in out Context)
   with Pre => Nkind (Callsite) in N_Subprogram_Call | N_Entry_Call_Statement;
   --  Similar to Process_Subprogram_Globals, this deals with the actuals
   --  provided in a subprogram call. The vertices are created but not linked
   --  up; as above, they are appended to Ins and various variants of Outs,
   --  depending on the parameter passing mechanism.

   use type Node_Lists.List;

   procedure Process_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with
     Post =>
       CM.Length = CM.Length'Old + 1
       and then Ctx'Old.Folded_Function_Checks = Ctx.Folded_Function_Checks;
   --  Process an arbitrary statement (this is basically a big case
   --  block which calls the various Do_XYZ procedures).

   procedure Process_Statement_List
     (L   : List_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   with Post => CM.Length = CM.Length'Old + 1;
   --  This processes a list of statements and links up each statement
   --  to the its successor. The final connection map for L will map
   --  to the standard entry of the first statement and the standard
   --  exits of the last statement.

   procedure Process_Subprogram_Globals
     (Callsite : Node_Id;
      Ins      : in out Vertex_Lists.List;
      Outs     : in out Vertex_Lists.List;
      FA       : in out Flow_Analysis_Graphs;
      CM       : in out Connection_Maps.Map;
      Ctx      : in out Context)
   with Pre => Nkind (Callsite) in N_Subprogram_Call | N_Entry_Call_Statement;
   --  This procedures creates the in and out vertices for a
   --  subprogram's globals. They are not connected to anything,
   --  instead the vertices are appended to Ins and Outs.

   procedure Reclaim_Borrower
     (Decl : Node_Id;
      FA   : in out Flow_Analysis_Graphs;
      Last : in out Flow_Graphs.Vertex_Id)
   with
     Pre  =>
       Nkind (Decl) = N_Object_Declaration
       and then Last /= Flow_Graphs.Null_Vertex,
     Post => Last /= Flow_Graphs.Null_Vertex;
   --  Creates a vertex that assigns a local borrower back to the corresponding
   --  borrowed object and links it up to Last. Then, Last is assigned with
   --  the created vertex, so this procedure can be called again with another
   --  borrower.

   function RHS_Split_Useful
     (LHS : Node_Or_Entity_Id; RHS : Node_Id; Scope : Flow_Scope)
      return Boolean
   with
     Pre =>
       (Nkind (LHS) in N_Subexpr
        or else Ekind (LHS) in E_Constant | E_Variable)
       and then Nkind (RHS) in N_Subexpr;
   --  Checks the right hand side of an assignment statement (or the
   --  expression on an object declaration) and determines if we can
   --  perform some meaningful record-field splitting.

   procedure Mark_Exceptional_Paths (FA : in out Flow_Analysis_Graphs);
   --  Set Is_Exceptional_Path on all vertices belonging to exceptional control
   --  flow or dead code, and Is_Exceptional_branch on all vertices leading
   --  into an exceptional path.

   procedure Prune_Dead_Paths (FA : in out Flow_Analysis_Graphs);
   --  Remove dead paths from the CFG

   procedure Prune_Exceptional_Paths (FA : in out Flow_Analysis_Graphs);
   --  Delete all vertices from exceptional paths from the control flow graph

   procedure Register_Own_Variable
     (FA : in out Flow_Analysis_Graphs; E : Entity_Id)
   with Pre => Ekind (E) in E_Abstract_State | E_Constant | E_Variable;
   --  Register E as an "owned" variable of a package, i.e. as a candidate to
   --  appear on the LHS of the generated Initialized.

   procedure Separate_Dead_Paths (FA : in out Flow_Analysis_Graphs);
   --  Make sure dead code remains separate from the rest of the control
   --  flow graph, so that the post-dominance frontier can be constructed
   --  without errors.

   procedure Simplify_CFG (FA : in out Flow_Analysis_Graphs);
   --  Remove all null vertices from the control flow graph

   function Pragma_Relevant_To_Flow (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_Pragma;
   --  Check if flow analysis cares about this particular pragma

   ------------------------------------------------------------
   --  Local procedures and functions
   ------------------------------------------------------------

   ----------------------
   -- Move_Connections --
   ----------------------

   procedure Move_Connections
     (CM : in out Connection_Maps.Map; Dst : Union_Id; Src : Union_Id)
   is
      Dst_Position : Connection_Maps.Cursor;
      Src_Position : Connection_Maps.Cursor;
      Inserted     : Boolean;
   begin
      --  This code is subtle, but efficient. It does only 2 lookups in the
      --  map (for Src and Dst) while avoiding tampering with cursors. Also, it
      --  avoids extra memory re-allocation by reusing the container from Src.

      CM.Insert (Key => Dst, Position => Dst_Position, Inserted => Inserted);

      pragma Assert (Inserted);

      Src_Position := CM.Find (Src);

      declare
         New_Connections : Graph_Connections renames CM (Dst_Position);
         Old_Connections : Graph_Connections renames CM (Src_Position);
      begin
         New_Connections.Standard_Entry := Old_Connections.Standard_Entry;
         Vertex_Sets.Move
           (Target => New_Connections.Standard_Exits,
            Source => Old_Connections.Standard_Exits);
      end;

      CM.Delete (Src_Position);
   end Move_Connections;

   ----------------------
   -- Add_Dummy_Vertex --
   ----------------------

   procedure Add_Dummy_Vertex
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
      V : Flow_Graphs.Vertex_Id;
   begin
      Add_Vertex (FA, Direct_Mapping_Id (N), Null_Node_Attributes, V);
      CM.Insert (Union_Id (N), Trivial_Connection (V));
   end Add_Dummy_Vertex;

   ----------------
   -- Add_Vertex --
   ----------------

   procedure Add_Vertex
     (FA : in out Flow_Analysis_Graphs; F : Flow_Id; A : V_Attributes)
   is
      V : Flow_Graphs.Vertex_Id;
   begin
      if F.Kind in Direct_Mapping | Record_Field then
         fndi (FA.Spec_Entity, F.Node);
      end if;
      FA.CFG.Add_Vertex (F, V);
      FA.Atr.Insert (V, A);
   end Add_Vertex;

   procedure Add_Vertex
     (FA : in out Flow_Analysis_Graphs;
      F  : Flow_Id;
      A  : V_Attributes;
      V  : out Flow_Graphs.Vertex_Id) is
   begin
      if F.Kind in Direct_Mapping | Record_Field then
         fndi (FA.Spec_Entity, F.Node);
      end if;
      FA.CFG.Add_Vertex (F, V);
      FA.Atr.Insert (V, A);
   end Add_Vertex;

   procedure Add_Vertex
     (FA : in out Flow_Analysis_Graphs;
      A  : V_Attributes;
      V  : out Flow_Graphs.Vertex_Id) is
   begin
      FA.CFG.Add_Vertex (V);
      FA.Atr.Insert (V, A);
   end Add_Vertex;

   ------------
   -- Linkup --
   ------------

   procedure Linkup
     (FA    : in out Flow_Analysis_Graphs;
      Froms : Vertex_Sets.Set;
      To    : Flow_Graphs.Vertex_Id) is
   begin
      for From of Froms loop
         Linkup (FA, From, To);
      end loop;
   end Linkup;

   procedure Linkup
     (FA   : in out Flow_Analysis_Graphs;
      From : Flow_Graphs.Vertex_Id;
      To   : Flow_Graphs.Vertex_Id)
   is
      function Get_Colour (V : Flow_Graphs.Vertex_Id) return Edge_Colours;
      --  Produce the correct colour for outbound edges depending on the
      --  execution kind of the given vertex.

      ----------------
      -- Get_Colour --
      ----------------

      function Get_Colour (V : Flow_Graphs.Vertex_Id) return Edge_Colours
      is (case FA.Atr (V).Execution is
            when Normal_Execution => EC_Default,
            when Barrier => EC_Barrier,
            when Abnormal_Termination => EC_Abend,
            when Infinite_Loop => EC_Inf);

      --  Local variables

      Col : Edge_Colours;

      From_Atr : V_Attributes renames FA.Atr (From);

      --  Start of processing for Linkup

   begin
      --  For parameter vertices we get the execution kind from their
      --  corresponding call vertex.

      if From_Atr.Is_Implicit_Parameter
        or else From_Atr.Is_Parameter
        or else From_Atr.Is_Global_Parameter
      then
         Col := Get_Colour (FA.CFG.Get_Vertex (From_Atr.Call_Vertex));

      --  For other vertices we get the execution kind from the vertex itself

      else
         Col := Get_Colour (From);
      end if;

      FA.CFG.Add_Edge (From, To, Col);
   end Linkup;

   ----------
   -- Join --
   ----------

   procedure Join
     (FA    : in out Flow_Analysis_Graphs;
      CM    : in out Connection_Maps.Map;
      Nodes : Union_Lists.List;
      Block : out Graph_Connections) is
   begin
      if Nodes.Is_Empty then
         declare
            V : Flow_Graphs.Vertex_Id;
         begin
            --  We had a null sequence so we need to produce a null node
            Add_Vertex (FA, Null_Node_Attributes, V);
            Block := Trivial_Connection (V);
         end;
      else
         Block.Standard_Entry := CM (Nodes.First_Element).Standard_Entry;

         declare
            Prev : Union_Lists.Cursor := Nodes.First;
            Curr : Union_Lists.Cursor := Union_Lists.Next (Prev);
         begin
            while Union_Lists.Has_Element (Curr) loop
               --  Connect this statement to the previous one
               Linkup
                 (FA,
                  CM (Nodes (Prev)).Standard_Exits,
                  CM (Nodes (Curr)).Standard_Entry);

               CM.Delete (Nodes (Prev));

               Prev := Curr;
               Curr := Union_Lists.Next (Curr);
            end loop;
         end;

         Block.Standard_Exits := CM (Nodes.Last_Element).Standard_Exits;

         CM.Delete (Nodes.Last_Element);
      end if;
   end Join;

   ------------------------
   -- Create_Record_Tree --
   ------------------------

   procedure Create_Record_Tree
     (F : Flow_Id; Leaf_Atr : V_Attributes; FA : in out Flow_Analysis_Graphs)
   is
   begin
      case F.Variant is
         when Normal_Use | In_View | Out_View =>
            raise Program_Error;

         when Initial_Value | Final_Value =>
            case F.Kind is
               when Null_Value | Synthetic_Null_Export =>
                  raise Program_Error;

               when Magic_String =>
                  null;

               when Direct_Mapping | Record_Field =>
                  if F.Kind = Record_Field
                    or else F.Facet in Private_Part | Extension_Part
                  then
                     declare
                        P : constant Flow_Id :=
                          Change_Variant
                            (Parent_Record (F),
                             Corresponding_Grouping (F.Variant));

                     begin
                        Create_Record_Tree (P, Leaf_Atr, FA);
                        case F.Variant is
                           when Initial_Value =>
                              Linkup
                                (FA,
                                 FA.CFG.Get_Vertex (P),
                                 FA.CFG.Get_Vertex (F));

                           when Final_Value =>
                              Linkup
                                (FA,
                                 FA.CFG.Get_Vertex (F),
                                 FA.CFG.Get_Vertex (P));

                           when others =>
                              raise Program_Error;
                        end case;
                     end;
                  end if;
            end case;

         when Initial_Grouping | Final_Grouping =>
            case F.Kind is
               --  Initial_Grouping and Final_Grouping only appear for
               --  variables represented by Entity_Id.

               when Null_Value | Synthetic_Null_Export | Magic_String =>
                  raise Program_Error;

               when Direct_Mapping | Record_Field =>
                  --  Only proceed if we don't have this vertex yet
                  if not FA.CFG.Contains (F) then
                     --  Create vertex
                     Add_Vertex
                       (FA, F, Make_Record_Tree_Attributes (Leaf_Atr));

                     if F.Kind = Record_Field then
                        Create_Record_Tree (Parent_Record (F), Leaf_Atr, FA);
                        case F.Variant is
                           when Initial_Grouping =>
                              Linkup
                                (FA,
                                 FA.CFG.Get_Vertex (Parent_Record (F)),
                                 FA.CFG.Get_Vertex (F));

                           when Final_Grouping =>
                              Linkup
                                (FA,
                                 FA.CFG.Get_Vertex (F),
                                 FA.CFG.Get_Vertex (Parent_Record (F)));

                           when others =>
                              raise Program_Error;
                        end case;
                     end if;
                  end if;
            end case;
      end case;
   end Create_Record_Tree;

   ---------------------------------------
   -- Create_Initial_And_Final_Vertices --
   ---------------------------------------

   procedure Create_Initial_And_Final_Vertices
     (E : Entity_Id; FA : in out Flow_Analysis_Graphs)
   is
      M : constant Param_Mode :=
        (case Ekind (E) is

           --  Formal parameters of mode IN with a visibly non-constant access
           --  type can be assigned in subprograms with side-effects, so we
           --  handle them very much like IN OUTs.

           when E_In_Parameter =>
             (if Is_Access_Variable (Etype (E))
                and then (Ekind (FA.Spec_Entity) in E_Procedure | E_Entry
                          or else Is_Function_With_Side_Effects
                                    (FA.Spec_Entity))
              then Mode_In_Out
              else Mode_In),

           when E_In_Out_Parameter | E_Task_Type => Mode_In_Out,

           when E_Function | E_Out_Parameter => Mode_Out,

           when E_Protected_Type =>
             (if Ekind (FA.Spec_Entity) = E_Function
              then Mode_In
              else Mode_In_Out),

           when E_Abstract_State | E_Constant | E_Loop_Parameter | E_Variable
           =>
             Mode_Invalid,

           when others => raise Program_Error);

      Scop : constant Flow_Scope :=
        (if FA.Generating_Globals or else Is_In_Analyzed_Files (E)
         then Null_Flow_Scope
         else FA.B_Scope);
      --  In phase 2, when this routine is called on constituents declared in
      --  private child packages, we need the scope of the parent package for
      --  deciding whether the constituent is initialized at elaboration. In
      --  phase 1 the initialization status of such constituents doesn't
      --  matter.

      procedure Process (F : Flow_Id)
      with
        Pre =>
          F.Kind in Direct_Mapping | Record_Field
          and then F.Variant = Normal_Use;

      -------------
      -- Process --
      -------------

      procedure Process (F : Flow_Id) is
         Initial_V, Final_V : Flow_Graphs.Vertex_Id;

         F_Initial : constant Flow_Id := Change_Variant (F, Initial_Value);
         F_Final   : constant Flow_Id := Change_Variant (F, Final_Value);

         Initial_Atr : constant V_Attributes :=
           Make_Variable_Attributes
             (F_Ent => F_Initial, Mode => M, E_Loc => E, S => Scop);

         Final_Atr : constant V_Attributes :=
           Make_Variable_Attributes (F_Ent => F_Final, Mode => M, E_Loc => E);

      begin
         --  Proof will pull reclamation functions at the end of the scope of
         --  E if its type needs reclamation.
         if Ekind (E) in E_Constant | E_Variable
           and then not Is_Library_Level_Entity (E)
         then
            Process_Reclamation_Functions (Etype (E), FA.Proof_Dependencies);
         end if;

         --  Setup the n'initial vertex. Note that initialization for
         --  variables is detected (and set) when building the flow graph
         --  for declarative parts.
         Add_Vertex (FA, F_Initial, Initial_Atr, Initial_V);
         Linkup (FA, Initial_V, FA.Start_Vertex);

         Create_Record_Tree (F_Initial, Initial_Atr, FA);

         --  Setup the n'final vertex
         Add_Vertex (FA, F_Final, Final_Atr, Final_V);
         Linkup (FA, FA.End_Vertex, Final_V);

         Create_Record_Tree (F_Final, Final_Atr, FA);

         FA.All_Vars.Insert (F);
      end Process;

      --  Start of processing for Create_Initial_And_Final_Vertices

   begin
      for Comp of Flatten_Variable (E, FA.B_Scope) loop
         Process (Comp);
      end loop;

      if Extensions_Visible (E, FA.B_Scope) then
         Process (Direct_Mapping_Id (E, Facet => Extension_Part));
      end if;

      if Ekind (E) in E_In_Out_Parameter | E_Out_Parameter
        and then Has_Discriminants (Get_Type (E, FA.B_Scope))
      then
         Process (Direct_Mapping_Id (E, Facet => The_Bounds));
      end if;
   end Create_Initial_And_Final_Vertices;

   procedure Create_Initial_And_Final_Vertices
     (F : Flow_Id; Mode : Param_Mode; FA : in out Flow_Analysis_Graphs)
   is
      procedure Process (F : Flow_Id)
      with
        Pre =>
          F.Kind in Direct_Mapping | Record_Field | Magic_String
          and then F.Variant = Normal_Use;

      -------------
      -- Process --
      -------------

      procedure Process (F : Flow_Id) is
         F_Initial : constant Flow_Id := Change_Variant (F, Initial_Value);
         F_Final   : constant Flow_Id := Change_Variant (F, Final_Value);

         Initial_Atr : constant V_Attributes :=
           Make_Global_Variable_Attributes (F => F_Initial, Mode => Mode);

         Final_Atr : constant V_Attributes :=
           Make_Global_Variable_Attributes (F => F_Final, Mode => Mode);

         Initial_V, Final_V : Flow_Graphs.Vertex_Id;
      begin
         --  Setup the F'initial vertex. Initialization is deduced from the
         --  mode.
         Add_Vertex (FA, F_Initial, Initial_Atr, Initial_V);
         Linkup (FA, Initial_V, FA.Start_Vertex);

         Create_Record_Tree (F_Initial, Initial_Atr, FA);

         --  Setup the F'final vertex
         Add_Vertex (FA, F_Final, Final_Atr, Final_V);
         Linkup (FA, FA.End_Vertex, Final_V);

         Create_Record_Tree (F_Final, Final_Atr, FA);

         FA.All_Vars.Insert (F);
      end Process;

      --  Start of processing for Create_Initial_And_Final_Vertices

   begin
      for Comp of Flatten_Variable (F, FA.B_Scope) loop
         Process (Comp);
      end loop;

      if Extensions_Visible (F, FA.B_Scope) then
         Process ((F with delta Facet => Extension_Part));
      end if;

      if F.Kind = Direct_Mapping
        and then Ekind (Get_Direct_Mapping_Id (F))
                 in E_In_Out_Parameter | E_Out_Parameter
        and then Has_Discriminants
                   (Get_Type (Get_Direct_Mapping_Id (F), FA.B_Scope))
      then
         Process ((F with delta Facet => The_Bounds));
      end if;
   end Create_Initial_And_Final_Vertices;

   -----------------------------
   -- Do_Assignment_Statement --
   -----------------------------

   procedure Do_Assignment_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      Funcalls : Call_Sets.Set;
      Indcalls : Node_Sets.Set;

      V : Flow_Graphs.Vertex_Id;

      Partial         : Boolean;
      View_Conversion : Boolean;
      LHS_Root        : Flow_Id;
      Vars_Defined    : Flow_Id_Sets.Set;
      Vars_Used       : Flow_Id_Sets.Set;
      Partial_Ext     : Boolean;
      Partial_Priv    : Boolean;

      LHS_Type : constant Entity_Id := Get_Type (Name (N), FA.B_Scope);
      To_Cw    : constant Boolean := Is_Class_Wide_Type (LHS_Type);

   begin
      --  Collect function calls appearing in the assignment statement: both
      --  its LHS and RHS.
      Pick_Generated_Info
        (N,
         FA.B_Scope,
         Function_Calls     => Funcalls,
         Indirect_Calls     => Indcalls,
         Proof_Dependencies => FA.Proof_Dependencies,
         Tasking            => FA.Tasking,
         Generating_Globals => FA.Generating_Globals);

      Process_Reclamation_Functions (LHS_Type, FA.Proof_Dependencies);

      --  Assignment with a function that has side effects is handled like a
      --  subprogram call: the function entity acts like a formal parameter
      --  of mode OUT and the LHS acts like the corresponding actual parameter.

      if Nkind (Expression (N)) = N_Function_Call
        and then Is_Function_With_Side_Effects
                   (Get_Called_Entity (Expression (N)))
      then
         Do_Call_Statement (Expression (N), FA, CM, Ctx);
         Move_Connections
           (CM, Dst => Union_Id (N), Src => Union_Id (Expression (N)));
         return;
      end if;

      --  First we need to determine the root name where we assign to, and
      --  whether this is a partial or full assignment. And work out which
      --  variables we define.

      Untangle_Assignment_Target
        (N                    => Name (N),
         Scope                => FA.B_Scope,
         View_Conversion      => View_Conversion,
         Map_Root             => LHS_Root,
         Use_Computed_Globals => not FA.Generating_Globals,
         Vars_Defined         => Vars_Defined,
         Vars_Used            => Vars_Used,
         Partial_Definition   => Partial,
         Partial_Ext          => Partial_Ext,
         Partial_Priv         => Partial_Priv);

      --  We have two scenarios: some kind of record assignment (in which case
      --  we try our best to dis-entangle the record fields so that information
      --  does not bleed all over the place) and the default case.

      if not Partial
        and then RHS_Split_Useful (Name (N), Expression (N), FA.B_Scope)
      then

         --  Deal with record self-assignments like we deal with calls to
         --  procedures with parameters of mode IN OUT, i.e. create separate
         --  vertices for each use and definition.
         --
         --  For a record self-assignment
         --
         --    Tmp := (A => Tmp.B, B => Tmp.A);
         --
         --  we produce the following CFG:
         --
         --     use {Tmp.B}
         --     |
         --     use {Tmp.A}
         --     |
         --     define {Tmp.A}
         --     |
         --     define {Tmp.B}
         --
         --  Each of the 'defined' vertices will also have Record_RHS set in
         --  its attributes so that we can fiddle the DDG to look like this:
         --
         --     use {Tmp.B} ------+
         --                       |
         --     use {Tmp.A} ------|--+
         --                       |  |
         --     define {Tmp.A} <--+  |
         --                          |
         --     define {Tmp.B} <-----+
         --
         --  Note that dependencies between the parameters are NOT set up here;
         --  this is done in Flow.Data_Depence_Graph.Create.

         declare
            Verts : Vertex_Lists.List;

            Verts_Defined : Vertex_Lists.List;
            --  Dedicated list with vertices for component definitions

            Cluster : Flow_Graphs.Cluster_Id;
            --  For grouping vertices corresponding to this object
            --  assignment in the visual representation of the graph.

            RHS_Map : Flow_Id_Maps.Map :=
              Untangle_Record_Assignment
                (Expression (N),
                 Map_Root                => LHS_Root,
                 Map_Type                => LHS_Type,
                 Target_Name             =>
                   (if Has_Target_Names (N) then LHS_Root else Null_Flow_Id),
                 Scope                   => FA.B_Scope,
                 Fold_Functions          => Inputs,
                 Use_Computed_Globals    => not FA.Generating_Globals,
                 Expand_Internal_Objects => False,
                 Extensions_Irrelevant   =>
                   not View_Conversion
                   and then not Is_Class_Wide_Type (LHS_Type));

            Empty_Reuse : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
            --  Optimize record assignments with no variable inputs, similar
            --  to what we do for record object declarations.

         begin
            --  If the LHS is a view conversion, filter the assigned fields
            --  and handle potential partial assignments in the extension and
            --  the private part.

            if View_Conversion then
               declare
                  Old_Map : constant Flow_Id_Maps.Map := RHS_Map;
               begin
                  RHS_Map.Clear;

                  for Field of Vars_Defined loop
                     declare
                        use Flow_Id_Maps;
                        Position : constant Flow_Id_Maps.Cursor :=
                          Find (Old_Map, Field);
                        pragma Assert (Has_Element (Position));
                     begin
                        RHS_Map.Insert (Key (Position), Old_Map (Position));
                     end;
                  end loop;

                  if Partial_Ext then
                     declare
                        The_Ext : constant Flow_Id :=
                          (LHS_Root with delta Facet => Extension_Part);
                     begin
                        RHS_Map (The_Ext).Include (The_Ext);
                     end;
                  end if;

                  if Partial_Priv then
                     declare
                        The_Priv : constant Flow_Id :=
                          (LHS_Root with delta Facet => Private_Part);
                     begin
                        RHS_Map (The_Priv).Include (The_Priv);
                     end;
                  end if;
               end;
            end if;

            --  Split out the assignment over a number of vertices
            for C in RHS_Map.Iterate loop
               declare
                  Output : Flow_Id renames Flow_Id_Maps.Key (C);
                  Inputs : Flow_Id_Sets.Set renames RHS_Map (C);

                  V_Used, V_Defined : Flow_Graphs.Vertex_Id;
                  --  Vertices for variables used and defined in a single
                  --  component assignment.

               begin
                  --  Reuse existing vertex for a field that uses no variable
                  --  inputs.

                  if Inputs.Is_Empty
                    and then Empty_Reuse /= Flow_Graphs.Null_Vertex
                  then
                     FA.Atr (Empty_Reuse).Variables_Defined.Insert (Output);
                  else
                     --  Create separate vertices with variables used and
                     --  defined. All variable uses happen first; then happen
                     --  all variable definitions. This is essential when
                     --  representing record self-assignments where several
                     --  components are read and then redefined.

                     Add_Vertex
                       (FA,
                        Make_Basic_Attributes
                          (Var_Ex_Use => Inputs,
                           Subp_Calls => Funcalls,
                           Indt_Calls => Indcalls,
                           Vertex_Ctx => Ctx.Vertex_Ctx,
                           E_Loc      => N,
                           Print_Hint => Pretty_Print_Record_Field),
                        V_Used);
                     Verts.Append (V_Used);

                     FA.Atr (V_Used).First_Field := Verts.First_Element;

                     Add_Vertex
                       (FA,
                        Make_Basic_Attributes
                          (Var_Def    => Flow_Id_Sets.To_Set (Output),
                           Subp_Calls => Funcalls,
                           Indt_Calls => Indcalls,
                           Vertex_Ctx => Ctx.Vertex_Ctx,
                           E_Loc      => N,
                           Print_Hint => Pretty_Print_Record_Field),
                        V_Defined);
                     Verts_Defined.Append (V_Defined);

                     FA.Atr (V_Defined).First_Field := Verts.First_Element;

                     --  Link variable use with variable definition. We will
                     --  add a data dependency edge when building DDG.
                     --  ??? This could be set in Make_Basic_Attributes to
                     --  avoid explicit manipulation of vertex attributes,
                     --  but then this routine would no longer be "Basic".
                     FA.Atr (V_Defined).Record_RHS := V_Used;

                     --  If this field uses no variable inputs, then we want
                     --  to reuse its vertex.

                     if Inputs.Is_Empty then
                        Empty_Reuse := V_Defined;
                     end if;
                  end if;
               end;
            end loop;

            --  Move vertices with variables defined to the end of list
            Verts.Splice
              (Before => Vertex_Lists.No_Element, Source => Verts_Defined);

            --  Assigning null records does not produce any assignments, so we
            --  create a null vertex instead.

            if Verts.Is_Empty then
               pragma Assert (Is_Null_Record_Type (LHS_Type));

               Add_Dummy_Vertex (N, FA, CM);

            --  Otherwise, we link all the vertices we have produced and update
            --  the connection map.

            else
               FA.CFG.New_Cluster (Cluster);
               V := Flow_Graphs.Null_Vertex;
               for W of Verts loop
                  if V /= Flow_Graphs.Null_Vertex then
                     Linkup (FA, V, W);
                  end if;
                  V := W;
                  FA.CFG.Set_Cluster (V, Cluster);
               end loop;

               CM.Insert
                 (Union_Id (N),
                  Graph_Connections'
                    (Standard_Entry => Verts.First_Element,
                     Standard_Exits => To_Set (Verts.Last_Element)));
            end if;
         end;

      else

         --  Work out the variables we use. These are the ones already
         --  used by the LHS + everything on the RHS.
         Vars_Used.Union
           (Get_Variables
              (Expression (N),
               Scope                => FA.B_Scope,
               Target_Name          =>
                 (if Has_Target_Names (N) then LHS_Root else Null_Flow_Id),
               Fold_Functions       => Inputs,
               Use_Computed_Globals => not FA.Generating_Globals,
               Consider_Extensions  => To_Cw));

         --  Any proof or null dependency variables need to be checked
         --  separately. We need to check both the LHS and RHS.
         Ctx.Folded_Function_Checks.Append (Expression (N));
         Ctx.Folded_Function_Checks.Append (Name (N));

         declare
            Var_Im_Use : Flow_Id_Sets.Set;
         begin
            if Partial then
               Var_Im_Use := Vars_Defined;
            else
               if Partial_Ext then
                  Var_Im_Use.Insert
                    ((LHS_Root with delta Facet => Extension_Part));
               end if;

               if Partial_Priv then
                  Var_Im_Use.Insert
                    ((LHS_Root with delta Facet => Private_Part));
               end if;
            end if;

            --  Produce the vertex
            Add_Vertex
              (FA,
               Direct_Mapping_Id (N),
               Make_Basic_Attributes
                 (Var_Def    => Vars_Defined,
                  Var_Ex_Use => Vars_Used,
                  Var_Im_Use => Var_Im_Use,
                  Subp_Calls => Funcalls,
                  Indt_Calls => Indcalls,
                  Vertex_Ctx => Ctx.Vertex_Ctx,
                  E_Loc      => N),
               V);
         end;

         CM.Insert (Union_Id (N), Trivial_Connection (V));
      end if;
   end Do_Assignment_Statement;

   -----------------------
   -- Do_Case_Statement --
   -----------------------

   procedure Do_Case_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V_Case            : Flow_Graphs.Vertex_Id;
      Alternative       : Node_Id;
      Funcalls          : Call_Sets.Set;
      Indcalls          : Node_Sets.Set;
      Known_Expression  : constant Boolean :=
        Compile_Time_Known_Value (Expression (N));
      Known_Alternative : constant Node_Id :=
        (if Known_Expression
         then Find_Static_Alternative (N)
         else Types.Empty);
   begin
      Pick_Generated_Info
        (Expression (N),
         FA.B_Scope,
         Function_Calls     => Funcalls,
         Indirect_Calls     => Indcalls,
         Proof_Dependencies => FA.Proof_Dependencies,
         Tasking            => FA.Tasking,
         Generating_Globals => FA.Generating_Globals);

      --  We have a vertex V for the case statement itself
      Add_Vertex
        (FA,
         Direct_Mapping_Id (N),
         Make_Basic_Attributes
           (Var_Ex_Use =>
              Get_Variables
                (Expression (N),
                 Scope                => FA.B_Scope,
                 Target_Name          => Null_Flow_Id,
                 Fold_Functions       => Inputs,
                 Use_Computed_Globals => not FA.Generating_Globals),
            Subp_Calls => Funcalls,
            Indt_Calls => Indcalls,
            Vertex_Ctx => Ctx.Vertex_Ctx,
            E_Loc      => N),
         V_Case);
      Ctx.Folded_Function_Checks.Append (Expression (N));
      CM.Insert
        (Union_Id (N),
         Graph_Connections'
           (Standard_Entry => V_Case, Standard_Exits => Empty_Set));

      Alternative := First_Non_Pragma (Alternatives (N));

      loop
         declare
            Stmts            : constant List_Id := Statements (Alternative);
            V_Alter          : Flow_Graphs.Vertex_Id;
            Dead_Alternative : constant Boolean :=
              Known_Expression and then Alternative /= Known_Alternative;
         begin
            --  We introduce a vertex V_Alter for each
            --  case_statement_alternative.
            Add_Vertex
              (FA,
               Direct_Mapping_Id (Alternative),
               Make_Aux_Vertex_Attributes
                 (E_Loc     => Alternative,
                  Execution =>
                    (if Is_Empty_Others (Alternative)
                     then Abnormal_Termination
                     else Normal_Execution)),
               V_Alter);

            --  We link V_Alter with its statements
            Process_Statement_List (Stmts, FA, CM, Ctx);
            Linkup (FA, V_Alter, CM (Union_Id (Stmts)).Standard_Entry);

            --  If the case alternative is not statically dead, we link
            --  V_Alter to V_Case and V_Alter to the standard exits of the
            --  case statement.
            if not Dead_Alternative then
               Linkup (FA, V_Case, V_Alter);
               CM (Union_Id (N)).Standard_Exits.Union
                 (CM (Union_Id (Stmts)).Standard_Exits);
            end if;

            CM.Delete (Union_Id (Stmts));

            Next_Non_Pragma (Alternative);

            exit when No (Alternative);
         end;
      end loop;

      --  We handle case statements with one alternative differently to case
      --  statements with more than one alternative.
      --  If there is just one case_statement_alternative then we introduce a
      --  control dependency on objects referenced in the selecting_expression.
      --  We do the same if the value of the expression is statically known.
      if List_Length (Alternatives (N)) = 1 or else Known_Expression then
         declare
            V_Dummy : Flow_Graphs.Vertex_Id;

         begin

            --  Even though this is not an entry barrier, we use Barrier for
            --  our execution type to draw a special edge.
            Add_Vertex
              (FA,
               Direct_Mapping_Id (Expression (N)),
               Make_Aux_Vertex_Attributes (E_Loc => N, Execution => Barrier),
               V_Dummy);
            Linkup (FA, V_Case, V_Dummy);

            CM (Union_Id (N)).Standard_Exits.Insert (V_Dummy);

         end;
      end if;
   end Do_Case_Statement;

   ---------------------------
   -- Do_Continue_Statement --
   ---------------------------

   procedure Do_Continue_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V        : Flow_Graphs.Vertex_Id;
      L        : Node_Id := N;
      Funcalls : Call_Sets.Set;
      Indcalls : Node_Sets.Set;
      Cond     : constant Node_Id := Condition (N);

      Mark : Borrowers_Markers.Cursor := Ctx.Borrow_Numbers.Last;
      --  Once we know which loop the continue statement refers to, it will
      --  point to the number of local borrowers in scope of that loop.

      Top : Node_Lists.Cursor := Ctx.Borrowers.Last;
      --  Iterator for the borrowers reclaimed when completing the current
      --  iteration.

      Position : Goto_Jump_Maps.Cursor;
      Unused   : Boolean;

   begin
      --  Go up the tree until we find the loop whose iteration we completes
      loop
         L := Parent (L);
         case Nkind (L) is
            when N_Loop_Statement =>
               --  When completing the iteration of a loop without name, we
               --  complete the iteration of the first loop; when there is
               --  a name, we look for the matching loop.
               if No (Name (N))
                 or else Entity (Identifier (L)) = Entity (Name (N))
               then
                  exit;
               end if;

            when N_Block_Statement =>
               Borrowers_Markers.Previous (Mark);

            when others =>
               null;
         end case;
      end loop;

      --  Conditional and unconditional continue are different. One requires an
      --  extra vertex, the other does not.

      if No (Cond) then
         Add_Vertex (FA, Direct_Mapping_Id (N), Null_Node_Attributes, V);
         CM.Insert
           (Union_Id (N),
            Graph_Connections'
              (Standard_Entry => V, Standard_Exits => Vertex_Sets.Empty_Set));

      else
         Pick_Generated_Info
           (Cond,
            FA.B_Scope,
            Function_Calls     => Funcalls,
            Indirect_Calls     => Indcalls,
            Proof_Dependencies => FA.Proof_Dependencies,
            Tasking            => FA.Tasking,
            Generating_Globals => FA.Generating_Globals);

         Add_Vertex
           (FA,
            Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Var_Ex_Use =>
                 Get_Variables
                   (Cond,
                    Scope                => FA.B_Scope,
                    Target_Name          => Null_Flow_Id,
                    Fold_Functions       => Inputs,
                    Use_Computed_Globals => not FA.Generating_Globals),
               Subp_Calls => Funcalls,
               Indt_Calls => Indcalls,
               Vertex_Ctx => Ctx.Vertex_Ctx,
               E_Loc      => N),
            V);
         Ctx.Folded_Function_Checks.Append (Cond);
         CM.Insert (Union_Id (N), Trivial_Connection (V));
      end if;

      --  When borrowers go out of scope, we pop them from the stack and
      --  assign back to the borrowed objects. This way we keep track of
      --  anything that happened while they were borrowed.

      for J in Ctx.Borrow_Numbers (Mark) + 1 .. Ctx.Borrowers.Length loop
         Reclaim_Borrower (Ctx.Borrowers (Top), FA, Last => V);
         Node_Lists.Previous (Top);
      end loop;

      Ctx.Goto_Jumps.Insert
        (Key      => Entity (Identifier (L)),
         New_Item => Vertex_Sets.Empty_Set,
         Position => Position,
         Inserted => Unused);
      Ctx.Goto_Jumps (Position).Insert (V);

   end Do_Continue_Statement;

   ------------------------
   -- Do_Delay_Statement --
   ------------------------

   procedure Do_Delay_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V         : Flow_Graphs.Vertex_Id;
      Vars_Used : Flow_Id_Sets.Set;
      Funcalls  : Call_Sets.Set;
      Indcalls  : Node_Sets.Set;

   begin
      --  Here we flag a delay statement as potentially blocking
      if FA.Generating_Globals and then FA.Has_Only_Nonblocking_Statements then
         FA.Has_Only_Nonblocking_Statements := False;
      end if;

      --  Gather variables used in the expression of the delay statement
      Vars_Used :=
        Get_Variables
          (Expression (N),
           Scope                => FA.B_Scope,
           Target_Name          => Null_Flow_Id,
           Fold_Functions       => Inputs,
           Use_Computed_Globals => not FA.Generating_Globals);

      --  Add the implicit use of Ada.Real_Time.Clock_Time or
      --  Ada.Calendar.Clock_Time, depending on the kind of the delay
      --  statement and (for the delay until) the base type of its expression.
      --  The condtion here is the same as in Expand_N_Delay_Until_Statement.
      Vars_Used.Include
        (Direct_Mapping_Id
           (RTE
              (case Nkind (N) is
                 when N_Delay_Relative_Statement => RE_Clock_Time,
                 when N_Delay_Until_Statement =>
                   (if Is_RTE (Base_Type (Etype (Expression (N))), RO_CA_Time)
                    then RO_CA_Clock_Time
                    else RE_Clock_Time),
                 when others => raise Program_Error)));

      Pick_Generated_Info
        (Expression (N),
         FA.B_Scope,
         Function_Calls     => Funcalls,
         Indirect_Calls     => Indcalls,
         Proof_Dependencies => FA.Proof_Dependencies,
         Tasking            => FA.Tasking,
         Generating_Globals => FA.Generating_Globals);

      Add_Vertex
        (FA,
         Direct_Mapping_Id (N),
         Make_Basic_Attributes
           (Var_Def    => Flow_Id_Sets.To_Set (Null_Export_Flow_Id),
            Var_Ex_Use => Vars_Used,
            Subp_Calls => Funcalls,
            Indt_Calls => Indcalls,
            Vertex_Ctx => Ctx.Vertex_Ctx,
            E_Loc      => N),
         V);
      Ctx.Folded_Function_Checks.Append (Expression (N));
      CM.Insert (Union_Id (N), Trivial_Connection (V));
   end Do_Delay_Statement;

   -----------------------
   -- Do_Exit_Statement --
   -----------------------

   procedure Do_Exit_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V        : Flow_Graphs.Vertex_Id;
      L        : Node_Id := N;
      Funcalls : Call_Sets.Set;
      Indcalls : Node_Sets.Set;
      Cond     : constant Node_Id := Condition (N);

      Mark : Borrowers_Markers.Cursor := Ctx.Borrow_Numbers.Last;
      --  Once we know which loop the EXIT statement refers to, it will point
      --  to the number of local borrowers in scope of that loop.

      Top : Node_Lists.Cursor := Ctx.Borrowers.Last;
      --  Iterator for the borrowers reclaimed when exiting the loop

   begin
      --  Go up the tree until we find the loop we are exiting from
      loop
         L := Parent (L);
         case Nkind (L) is
            when N_Loop_Statement =>
               --  When exiting without name, we exit at the first loop;
               --  when exiting with name, we look for the matching loop.
               if No (Name (N))
                 or else Entity (Identifier (L)) = Entity (Name (N))
               then
                  exit;
               end if;

            when N_Block_Statement =>
               Borrowers_Markers.Previous (Mark);

            when others =>
               null;
         end case;
      end loop;

      --  Conditional and unconditional exits are different. One
      --  requires an extra vertex, the other does not.
      if No (Cond) then
         Add_Vertex (FA, Direct_Mapping_Id (N), Null_Node_Attributes, V);
         CM.Insert
           (Union_Id (N),
            Graph_Connections'
              (Standard_Entry => V, Standard_Exits => Vertex_Sets.Empty_Set));

      else
         Pick_Generated_Info
           (Cond,
            FA.B_Scope,
            Function_Calls     => Funcalls,
            Indirect_Calls     => Indcalls,
            Proof_Dependencies => FA.Proof_Dependencies,
            Tasking            => FA.Tasking,
            Generating_Globals => FA.Generating_Globals);

         Add_Vertex
           (FA,
            Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Var_Ex_Use =>
                 Get_Variables
                   (Cond,
                    Scope                => FA.B_Scope,
                    Target_Name          => Null_Flow_Id,
                    Fold_Functions       => Inputs,
                    Use_Computed_Globals => not FA.Generating_Globals),
               Subp_Calls => Funcalls,
               Indt_Calls => Indcalls,
               Vertex_Ctx => Ctx.Vertex_Ctx,
               E_Loc      => N),
            V);
         Ctx.Folded_Function_Checks.Append (Cond);
         CM.Insert (Union_Id (N), Trivial_Connection (V));
      end if;

      --  When borrowers go out of scope, we pop them from the stack and
      --  assign back to the borrowed objects. This way we keep track of
      --  anything that happened while they were borrowed.

      for J in Ctx.Borrow_Numbers (Mark) + 1 .. Ctx.Borrowers.Length loop
         Reclaim_Borrower (Ctx.Borrowers (Top), FA, Last => V);
         Node_Lists.Previous (Top);
      end loop;

      CM (Union_Id (L)).Standard_Exits.Insert (V);
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
      Ret_Object   : constant Entity_Id := Get_Return_Object (N);
      HSS          : constant Node_Id := Handled_Statement_Sequence (N);

   begin
      --  We create a null vertex for the extended return statement
      Add_Vertex (FA, Direct_Mapping_Id (N), Null_Node_Attributes, V);
      --  Control flows in, but we do not flow out again
      CM.Insert
        (Union_Id (N),
         Graph_Connections'(Standard_Entry => V, Standard_Exits => Empty_Set));

      --  Store the extended return node in context, because it cannot be
      --  retrieved from the AST when we see a simple_return_statement.
      Ctx.Extended_Return := N;

      --  Process the statements of Ret_Object_L
      Process_Statement_List (Ret_Object_L, FA, CM, Ctx);

      --  Link the entry vertex V (the extended return statement) to
      --  standard entry of its return_object_declarations.
      Linkup (FA, V, CM (Union_Id (Ret_Object_L)).Standard_Entry);

      Add_Vertex
        (FA,
         Direct_Mapping_Id (Ret_Entity),
         Make_Extended_Return_Attributes
           (Var_Def         => Flatten_Variable (FA.Spec_Entity, FA.B_Scope),
            Var_Use         => Flatten_Variable (Ret_Object, FA.B_Scope),
            Object_Returned => Ret_Object,
            Vertex_Ctx      => Ctx.Vertex_Ctx,
            E_Loc           => Ret_Entity),
         V);

      if Present (HSS) then
         --  We process the sequence of statements
         Process_Statement (HSS, FA, CM, Ctx);

         --  We link the standard exits of Ret_Object_L to the standard entry
         --  of the sequence of statements.
         Linkup
           (FA,
            CM (Union_Id (Ret_Object_L)).Standard_Exits,
            CM (Union_Id (HSS)).Standard_Entry);

         --  We link the standard exits of the sequence of statements to the
         --  standard entry of the implicit return statement.
         Linkup (FA, CM (Union_Id (HSS)).Standard_Exits, V);

         CM.Delete (Union_Id (HSS));
      else
         --  No sequence of statements is present. We link the
         --  standard exits of Ret_Object_L to the implicit return
         --  statement.
         Linkup (FA, CM (Union_Id (Ret_Object_L)).Standard_Exits, V);
      end if;

      CM.Delete (Union_Id (Ret_Object_L));
      Ctx.Extended_Return := Types.Empty;

      --  When borrowers go out of scope, we pop them from the stack and
      --  assign back to the borrowed objects. This way we keep track of
      --  anything that happened while they were borrowed.

      for Decl of reverse Ctx.Borrowers loop
         Reclaim_Borrower (Decl, FA, Last => V);
      end loop;

      --  We link the implicit return statement to the helper end vertex
      Linkup (FA, V, FA.Helper_End_Vertex);
   end Do_Extended_Return_Statement;

   -----------------------
   -- Do_Goto_Statement --
   -----------------------

   procedure Do_Goto_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V        : Flow_Graphs.Vertex_Id;
      Position : Goto_Jump_Maps.Cursor;
      Unused   : Boolean;

      Target_Label_Parent : constant Node_Id :=
        Statement_Enclosing_Label (Entity (Name (N)));

      Par : Node_Id := N;
      --  Iterator for finding the parent of the target label

      Mark : Borrowers_Markers.Cursor := Ctx.Borrow_Numbers.Last;
      --  Once we know which sequence_of_statements we will jump to, it will
      --  point to the number of local borrowers at that point.

      Top : Node_Lists.Cursor := Ctx.Borrowers.Last;
      --  Iterator for the borrowers reclaimed when jumping with goto

   begin
      --  Go up the tree until we find the parent of the sequence_of_statements
      --  we are jumping to and move the cursor at each block that we jump out
      --  from.
      loop
         Par := Parent (Par);
         exit when Par = Target_Label_Parent;
         if Nkind (Par) = N_Block_Statement then
            Borrowers_Markers.Previous (Mark);
         end if;
      end loop;

      Add_Vertex (FA, Direct_Mapping_Id (N), Null_Node_Attributes, V);
      CM.Insert
        (Union_Id (N),
         Graph_Connections'
           (Standard_Entry => V, Standard_Exits => Vertex_Sets.Empty_Set));

      --  When borrowers go out of scope, we pop them from the stack and
      --  assign back to the borrowed objects. This way we keep track of
      --  anything that happened while they were borrowed.

      for J in Ctx.Borrow_Numbers (Mark) + 1 .. Ctx.Borrowers.Length loop
         Reclaim_Borrower (Ctx.Borrowers (Top), FA, Last => V);
         Node_Lists.Previous (Top);
      end loop;

      Ctx.Goto_Jumps.Insert
        (Key      => Entity (Name (N)),
         New_Item => Vertex_Sets.Empty_Set,
         Position => Position,
         Inserted => Unused);
      Ctx.Goto_Jumps (Position).Include (V);
   end Do_Goto_Statement;

   ---------------------------------------
   -- Do_Handled_Sequence_Of_Statements --
   ---------------------------------------

   procedure Do_Handled_Sequence_Of_Statements
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      Handler : Node_Id;
      HStmts  : List_Id;
      Stmts   : constant List_Id := Statements (N);
   begin
      --  Borrowers might be declared both in block statements and extended
      --  return statements, but both these constructs include a handled
      --  sequence of statements, so it is better to handle both of them here.

      Ctx.Borrow_Numbers.Append (Ctx.Borrowers.Length);

      --  We first process exception handlers, so when a statement from the
      --  handled sequence of statements raises an exception, it can be linked
      --  straight to the exception handler. Otherwise, we would need to store
      --  vertices where exceptions are raised and link them to vertices for
      --  the handlers afterwards.

      --  We don't expect any meaningful pragma at the beginning of exception
      --  handlers.

      Handler := First_Non_Pragma (Exception_Handlers (N));

      while Present (Handler) loop
         HStmts := Statements (Handler);

         Process_Statement_List (HStmts, FA, CM, Ctx);

         --  It is more convenient to connect a raise statement with the node
         --  of the exception handler and not with the list of its statements,
         --  so move the connections.

         Move_Connections
           (CM, Dst => Union_Id (Handler), Src => Union_Id (HStmts));

         Next_Non_Pragma (Handler);
      end loop;

      --  Now process the handed statements themselves

      Process_Statement_List (Stmts, FA, CM, Ctx);
      Move_Connections (CM, Dst => Union_Id (N), Src => Union_Id (Stmts));

      --  Finally, combine standard exits of the normal execution and
      --  exception handlers and forget about the handlers, since they can't
      --  be referenced anymore.

      Handler := First_Non_Pragma (Exception_Handlers (N));
      while Present (Handler) loop
         declare
            Handler_Connections : Connection_Maps.Cursor :=
              CM.Find (Union_Id (Handler));
         begin
            CM (Union_Id (N)).Standard_Exits.Union
              (CM (Handler_Connections).Standard_Exits);

            CM.Delete (Handler_Connections);
         end;

         Next_Non_Pragma (Handler);
      end loop;

      --  Local borrowers cease to exist when exiting the handled sequence of
      --  statements.

      Ctx.Borrow_Numbers.Delete_Last;
   end Do_Handled_Sequence_Of_Statements;

   ---------------------
   -- Do_If_Statement --
   ---------------------

   procedure Do_If_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is

      function Is_Statically_Disabled (N : Node_Id) return Boolean
      with Pre => Nkind (N) in N_Subexpr and then Is_Boolean_Type (Etype (N));
      --  Checks if N is a statically disabled condition, no matter what it
      --  evaluates to.

      ----------------------------
      -- Is_Statically_Disabled --
      ----------------------------

      function Is_Statically_Disabled (N : Node_Id) return Boolean
      is (Exp_Util.Is_Statically_Disabled
            (N => N, Value => True, Include_Valid => False)
          or else Exp_Util.Is_Statically_Disabled
                    (N => N, Value => False, Include_Valid => False));

      V, V_Prev           : Flow_Graphs.Vertex_Id;
      If_Part             : constant List_Id := Then_Statements (N);
      Else_Part           : constant List_Id := Else_Statements (N);
      Elsif_Part          : constant List_Id := Elsif_Parts (N);
      Elsif_Statement     : Node_Id;
      Funcalls            : Call_Sets.Set;
      Indcalls            : Node_Sets.Set;
      Seen_True_Condition : Boolean := False;
      Known_Condition     : Boolean :=
        Compile_Time_Known_Value (Condition (N));
      Seen_True_Warn_Off  : Boolean :=
        Exp_Util.Is_Statically_Disabled
          (N => Condition (N), Value => True, Include_Valid => False);
      Save_Warn_Off       : constant Boolean := Ctx.Vertex_Ctx.Warnings_Off;

   begin
      --  We have a vertex for the if statement itself
      Pick_Generated_Info
        (Condition (N),
         FA.B_Scope,
         Function_Calls     => Funcalls,
         Indirect_Calls     => Indcalls,
         Proof_Dependencies => FA.Proof_Dependencies,
         Tasking            => FA.Tasking,
         Generating_Globals => FA.Generating_Globals);

      --  Disable warnings on the if statement itself when the condition is
      --  statically disabled, no matter its value.
      Ctx.Vertex_Ctx.Warnings_Off :=
        Save_Warn_Off or else Is_Statically_Disabled (Condition (N));

      Add_Vertex
        (FA,
         Direct_Mapping_Id (N),
         Make_Basic_Attributes
           (Var_Ex_Use =>
              Get_Variables
                (Condition (N),
                 Scope                => FA.B_Scope,
                 Target_Name          => Null_Flow_Id,
                 Fold_Functions       => Inputs,
                 Use_Computed_Globals => not FA.Generating_Globals),
            Subp_Calls => Funcalls,
            Indt_Calls => Indcalls,
            Vertex_Ctx => Ctx.Vertex_Ctx,
            E_Loc      => N),
         V);
      Ctx.Folded_Function_Checks.Append (Condition (N));
      CM.Insert
        (Union_Id (N),
         Graph_Connections'(Standard_Entry => V, Standard_Exits => Empty_Set));

      --  We don't want to emit warnings about unreachable code on the if part
      --  statements either when we are already in such a case, or when the if
      --  condition is statically disabled.
      Ctx.Vertex_Ctx.Warnings_Off :=
        Save_Warn_Off
        or else Exp_Util.Is_Statically_Disabled
                  (N => Condition (N), Value => False, Include_Valid => False);

      --  We hang the if part off that
      Process_Statement_List (If_Part, FA, CM, Ctx);

      --  We restore the context after the if part, and if the if condition is
      --  statically disabled, we won't emit warnings about unreachable
      --  code on following elsif/else conditions nor the statements.
      Ctx.Vertex_Ctx.Warnings_Off := Save_Warn_Off or else Seen_True_Warn_Off;

      --  The statements in the if branch are linked to the if statement vertex
      --  and the standard exits of the if statement if they are not statically
      --  dead.

      if not Known_Condition or else Is_True (Expr_Value (Condition (N))) then
         Seen_True_Condition := Known_Condition;
         Linkup (FA, V, CM (Union_Id (If_Part)).Standard_Entry);
         CM (Union_Id (N)).Standard_Exits.Union
           (CM (Union_Id (If_Part)).Standard_Exits);
      end if;

      CM.Delete (Union_Id (If_Part));

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
      --
      --  If we encounter a condition known to be true, Has_Encountered_True
      --  is set to True. The remaining branches of the if statement will
      --  not be linked to the graph, because they are statically dead.
      --
      --  If we encounter a condition known to be false, the statements of
      --  the branch are not linked to the vertex representing elsif vertex.

      if Present (Elsif_Part) then
         Elsif_Statement := First (Elsif_Part);
         V_Prev := V;

         while Present (Elsif_Statement) loop
            Known_Condition :=
              Compile_Time_Known_Value (Condition (Elsif_Statement));
            Seen_True_Warn_Off :=
              Seen_True_Warn_Off
              or else Exp_Util.Is_Statically_Disabled
                        (N             => Condition (Elsif_Statement),
                         Value         => True,
                         Include_Valid => False);

            declare
               Elsif_Body  : constant List_Id :=
                 Then_Statements (Elsif_Statement);
               Funcalls    : Call_Sets.Set;
               Dead_Branch : constant Boolean :=
                 Seen_True_Condition
                 or else (Known_Condition
                          and then Is_False
                                     (Expr_Value
                                        (Condition (Elsif_Statement))));
            begin

               --  We have a vertex V for each elsif statement
               Pick_Generated_Info
                 (Condition (Elsif_Statement),
                  FA.B_Scope,
                  Function_Calls     => Funcalls,
                  Indirect_Calls     => Indcalls,
                  Proof_Dependencies => FA.Proof_Dependencies,
                  Tasking            => FA.Tasking,
                  Generating_Globals => FA.Generating_Globals);

               --  Disable warnings on the elsif statement itself when the
               --  condition is statically disabled, no matter its value.
               Ctx.Vertex_Ctx.Warnings_Off :=
                 Ctx.Vertex_Ctx.Warnings_Off
                 or else Is_Statically_Disabled (Condition (Elsif_Statement));

               Add_Vertex
                 (FA,
                  Direct_Mapping_Id (Elsif_Statement),
                  Make_Basic_Attributes
                    (Var_Ex_Use =>
                       Get_Variables
                         (Condition (Elsif_Statement),
                          Scope                => FA.B_Scope,
                          Target_Name          => Null_Flow_Id,
                          Fold_Functions       => Inputs,
                          Use_Computed_Globals => not FA.Generating_Globals),
                     Subp_Calls => Funcalls,
                     Indt_Calls => Indcalls,
                     Vertex_Ctx => Ctx.Vertex_Ctx,
                     E_Loc      => Elsif_Statement),
                  V);
               Ctx.Folded_Function_Checks.Append (Condition (Elsif_Statement));

               --  If we didn't encounter a statically true condition, link
               --  V_Prev to V.

               if not Seen_True_Condition then
                  Linkup (FA, V_Prev, V);
               end if;

               --  Like the if part, we set the correct context for warning
               --  emission about unreachable code.
               Ctx.Vertex_Ctx.Warnings_Off :=
                 Ctx.Vertex_Ctx.Warnings_Off
                 or else Exp_Util.Is_Statically_Disabled
                           (N             => Condition (Elsif_Statement),
                            Value         => False,
                            Include_Valid => False);

               --  Process statements of elsif
               Process_Statement_List (Elsif_Body, FA, CM, Ctx);

               --  We restore the context afterwards
               Ctx.Vertex_Ctx.Warnings_Off :=
                 Save_Warn_Off or else Seen_True_Warn_Off;

               --  If the code is not statically dead, link V to the
               --  statements of elsif and add the exits of Elsif_Body to the
               --  exits of N.

               if not Dead_Branch then
                  Seen_True_Condition :=
                    Seen_True_Condition or else Known_Condition;

                  Linkup (FA, V, CM (Union_Id (Elsif_Body)).Standard_Entry);

                  CM (Union_Id (N)).Standard_Exits.Union
                    (CM (Union_Id (Elsif_Body)).Standard_Exits);
               end if;

               CM.Delete (Union_Id (Elsif_Body));
            end;

            V_Prev := V;
            Next (Elsif_Statement);
         end loop;
      end if;

      --  Remember that V is the vertex associated with either the
      --  last elsif blob or the if statement itself.

      if Present (Else_Part) then
         Ctx.Vertex_Ctx.Warnings_Off :=
           Ctx.Vertex_Ctx.Warnings_Off or else Seen_True_Warn_Off;
         Process_Statement_List (Else_Part, FA, CM, Ctx);

         if not Seen_True_Condition then
            Linkup (FA, V, CM (Union_Id (Else_Part)).Standard_Entry);

            CM (Union_Id (N)).Standard_Exits.Union
              (CM (Union_Id (Else_Part)).Standard_Exits);
         end if;

         CM.Delete (Union_Id (Else_Part));

      --  If we didn't encounter a statically true condition, then we could
      --  exit the if statement by the last elsif statement.

      elsif not Seen_True_Condition then
         CM (Union_Id (N)).Standard_Exits.Insert (V);
      end if;

      --  Context is restored after processing the if statement
      Ctx.Vertex_Ctx.Warnings_Off := Save_Warn_Off;
   end Do_If_Statement;

   --------------
   -- Do_Label --
   --------------

   procedure Do_Label
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V : Flow_Graphs.Vertex_Id;
      C : Goto_Jump_Maps.Cursor :=
        Ctx.Goto_Jumps.Find (Entity (Identifier (N)));

   begin
      Add_Vertex (FA, Direct_Mapping_Id (N), Null_Node_Attributes, V);

      CM.Insert (Union_Id (N), Trivial_Connection (V));

      if Goto_Jump_Maps.Has_Element (C) then
         Linkup (FA, Froms => Ctx.Goto_Jumps (C), To => V);
         Ctx.Goto_Jumps.Delete (C);
      end if;
   end Do_Label;

   -----------------------
   -- Do_Loop_Statement --
   -----------------------

   procedure Do_Loop_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      Potentially_Neverending_Vertex : Flow_Graphs.Vertex_Id;
      --  Stores the vertex id that will be flagged as neverending if
      --  necessary.

      function Is_For_Loop (N : Node_Id) return Boolean
      is (Nkind (N) = N_Loop_Statement
          and then Present (Iteration_Scheme (N))
          and then Present
                     (Loop_Parameter_Specification (Iteration_Scheme (N))));
      --  Check if the given loop is a simple for loop

      function Get_Filter_Variables (Expr : Node_Id) return Flow_Id_Sets.Set
      is (if Present (Expr)
          then
            Get_Variables
              (N                    => Expr,
               Scope                => FA.B_Scope,
               Target_Name          => Null_Flow_Id,
               Fold_Functions       => Inputs,
               Use_Computed_Globals => not FA.Generating_Globals)
          else Flow_Id_Sets.Empty_Set)
      with Pre => (if Present (Expr) then Nkind (Expr) in N_Subexpr);
      --  If Expr is not an empty node, returns the set of variables
      --  read in the filter expression. Otherwise, returns an empty set.

      function Get_Loop_Variable (N : Node_Id) return Entity_Id
      is (Defining_Identifier
            (Loop_Parameter_Specification (Iteration_Scheme (N))))
      with
        Pre  => Is_For_Loop (N),
        Post => Ekind (Get_Loop_Variable'Result) = E_Loop_Parameter;
      --  Obtain the entity of a for loops loop parameter

      function Get_Loop_Range (N : Node_Id) return Node_Id
      with Pre => Is_For_Loop (N);
      --  Return the range given for loop

      function Loop_Might_Exit_Early (Loop_N : Node_Id) return Boolean
      with Pre => Nkind (Loop_N) = N_Loop_Statement;
      --  Return true if the loop contains an exit or return statement

      procedure Linkup_Continue_Statements (V : Flow_Graphs.Vertex_Id);
      --  Link vertices of continue statements targeting the loop to V, and
      --  then remove them from the context.

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
      --  also flagged as Is_Initialized so that it can be suitably
      --  ignored by subsequent analysis).
      --
      --  We distinguish this case (non-empty range) from the previous
      --  one (unknown range) as subsequent code may rely on any
      --  initializations in the loop body.

      procedure Do_Iterator_Loop;
      --  Helper procedure to deal with for loops using iterators. Very
      --  similar to general for loops, except that we always produce
      --  unknown-if-executed loops.
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
      --  This means the loop body may not be executed, so any initializations
      --  in the loop which subsequent code depends on will be flagged up.

      function Variables_Initialized_By_Loop
        (Loop_N : Node_Id) return Flow_Id_Sets.Set
      with Pre => Nkind (N) = N_Loop_Statement;
      --  A conservative heuristic to determine the set of possible variables
      --  fully initialized by the given statement list.

      --------------------
      -- Get_Loop_Range --
      --------------------

      function Get_Loop_Range (N : Node_Id) return Node_Id is
         DSD : constant Node_Id :=
           Discrete_Subtype_Definition
             (Loop_Parameter_Specification (Iteration_Scheme (N)));

      begin
         pragma
           Assert
             (Nkind (DSD)
              in N_Range
               | N_Subtype_Indication
               | N_Identifier
               | N_Expanded_Name);

         return Get_Range (DSD);
      end Get_Loop_Range;

      --------------------------------
      -- Linkup_Continue_Statements --
      --------------------------------

      procedure Linkup_Continue_Statements (V : Flow_Graphs.Vertex_Id) is
         C : Goto_Jump_Maps.Cursor :=
           Ctx.Goto_Jumps.Find (Entity (Identifier (N)));
      begin
         if Goto_Jump_Maps.Has_Element (C) then
            Linkup (FA, Froms => Ctx.Goto_Jumps (C), To => V);
            Ctx.Goto_Jumps.Delete (C);
         end if;
      end Linkup_Continue_Statements;

      -------------
      -- Do_Loop --
      -------------

      procedure Do_Loop is
         function Proc (N : Node_Id) return Traverse_Result;
         --  Set Contains_Return to true if we find a return statement

         ----------
         -- Proc --
         ----------

         function Proc (N : Node_Id) return Traverse_Result is
         begin
            case Nkind (N) is

               --  These might cause the loop to exit early

               when N_Simple_Return_Statement | N_Extended_Return_Statement =>
                  return Abandon;

               --  In these the EXIT/RETURN statement, if present, will
               --  certainly refer to subprogram's own loop (EXIT) or to
               --  the suprogram itself (RETURN).

               when N_Subprogram_Body
                  | N_Subprogram_Declaration
                  | N_Package_Declaration
                  | N_Package_Body
                  | N_Generic_Declaration
               =>
                  return Skip;

               when others =>
                  return OK;
            end case;
         end Proc;

         function Find_Return is new Traverse_More_Func (Process => Proc);

         Contains_Return : constant Boolean := Find_Return (N) = Abandon;
         --  True if we have a return statement

         V           : Flow_Graphs.Vertex_Id;
         Faux_Exit_V : Flow_Graphs.Vertex_Id;

         --  Start of processing for Do_Loop

      begin
         --  The important attributes here are Is_Null_Node equal False (to
         --  prevent simplification of neverending loops), Is_Program_Node
         --  equal False (to prevent warning about ineffective statements)
         --  and Error_Location (to attach errors about neverending loops).
         --
         --  Other attributes are just for consistency.

         Add_Vertex
           (FA,
            Direct_Mapping_Id (N),
            (Null_Attributes
             with delta
               Error_Location    => N,
               In_Nested_Package => Ctx.Vertex_Ctx.In_Nested_Package,
               Loops             => Ctx.Vertex_Ctx.Current_Loops,
               Warnings_Off      => Ctx.Vertex_Ctx.Warnings_Off),
            V);

         --  Entry point for the loop is V
         CM (Union_Id (N)).Standard_Entry := V;

         --  Set Potentially_Neverending_Vertex to the added vertex
         Potentially_Neverending_Vertex := V;

         --  Exit from the loop is at the end of the loop, i.e. we are
         --  always going round at least once.
         if Contains_Return then
            --  If the loop contains a return statement we do not add
            --  the faux exit.
            null;
         elsif not CM (Union_Id (N)).Standard_Exits.Is_Empty then
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
               Make_Aux_Vertex_Attributes
                 (E_Loc => N, Execution => Infinite_Loop),
               Faux_Exit_V);

            --  We now thread this at the back of the connection map
            --  for Statements (N). Sorry, this is really quite ugly.
            Linkup
              (FA, CM (Union_Id (Statements (N))).Standard_Exits, Faux_Exit_V);
            CM (Union_Id (Statements (N))).Standard_Exits :=
              Vertex_Sets.To_Set (Faux_Exit_V);

            --  We add a mark the faux exit vertex as a possible
            --  exit of this loop.
            CM (Union_Id (N)).Standard_Exits.Insert (Faux_Exit_V);

            --  Finally, we set Potentially_Neverending_Vertex to the faux exit
            --  vertex, because vertex V could be removed in Simplify_CFG if it
            --  is null.
            Potentially_Neverending_Vertex := Faux_Exit_V;
         end if;

         --  Loop the loop: V -> body -> V
         Linkup (FA, V, CM (Union_Id (Statements (N))).Standard_Entry);
         Linkup (FA, CM (Union_Id (Statements (N))).Standard_Exits, V);

         Linkup_Continue_Statements (V);
      end Do_Loop;

      -------------------
      -- Do_While_Loop --
      -------------------

      procedure Do_While_Loop is
         V        : Flow_Graphs.Vertex_Id;
         Funcalls : Call_Sets.Set;
         Indcalls : Node_Sets.Set;
      begin
         Pick_Generated_Info
           (Condition (Iteration_Scheme (N)),
            FA.B_Scope,
            Function_Calls     => Funcalls,
            Indirect_Calls     => Indcalls,
            Proof_Dependencies => FA.Proof_Dependencies,
            Tasking            => FA.Tasking,
            Generating_Globals => FA.Generating_Globals);

         Add_Vertex
           (FA,
            Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Var_Ex_Use =>
                 Get_Variables
                   (Condition (Iteration_Scheme (N)),
                    Scope                => FA.B_Scope,
                    Target_Name          => Null_Flow_Id,
                    Fold_Functions       => Inputs,
                    Use_Computed_Globals => not FA.Generating_Globals),
               Subp_Calls => Funcalls,
               Indt_Calls => Indcalls,
               Vertex_Ctx => Ctx.Vertex_Ctx,
               E_Loc      => N),
            V);
         Ctx.Folded_Function_Checks.Append (Condition (Iteration_Scheme (N)));

         --  Flow for the while loops goes into the condition and then
         --  out again.
         CM (Union_Id (N)).Standard_Entry := V;
         CM (Union_Id (N)).Standard_Exits.Insert (V);

         --  Loop the loop: V -> body -> V
         Linkup (FA, V, CM (Union_Id (Statements (N))).Standard_Entry);
         Linkup (FA, CM (Union_Id (Statements (N))).Standard_Exits, V);

         Linkup_Continue_Statements (V);

         --  Set Potentially_Neverending_Vertex to the added vertex
         Potentially_Neverending_Vertex := V;
      end Do_While_Loop;

      -----------------
      -- Do_For_Loop --
      -----------------

      procedure Do_For_Loop (Fully_Initialized : out Flow_Id_Sets.Set) is
         LPS : constant Node_Id :=
           Loop_Parameter_Specification (Iteration_Scheme (N));

         LP : constant Entity_Id := Defining_Identifier (LPS);

         DSD    : constant Node_Id := Discrete_Subtype_Definition (LPS);
         R      : constant Node_Id := Get_Loop_Range (N);
         LB     : constant Node_Id := Low_Bound (R);
         HB     : constant Node_Id := High_Bound (R);
         Filter : constant Node_Id := Iterator_Filter (LPS);
         Vars   : constant Flow_Id_Sets.Set :=
           Get_Variables
             (N                    => LB,
              Scope                => FA.B_Scope,
              Target_Name          => Null_Flow_Id,
              Fold_Functions       => Inputs,
              Use_Computed_Globals => not FA.Generating_Globals)
           or Get_Variables
                (N                    => HB,
                 Scope                => FA.B_Scope,
                 Target_Name          => Null_Flow_Id,
                 Fold_Functions       => Inputs,
                 Use_Computed_Globals => not FA.Generating_Globals)
           or Get_Filter_Variables (Filter);

         V        : Flow_Graphs.Vertex_Id;
         Funcalls : Call_Sets.Set;
         Indcalls : Node_Sets.Set;
      begin
         --  We have a new variable here which we have not picked up
         --  in Create, so we should set it up.
         Create_Initial_And_Final_Vertices (LP, FA);

         Pick_Generated_Info
           (DSD,
            FA.B_Scope,
            Function_Calls     => Funcalls,
            Indirect_Calls     => Indcalls,
            Proof_Dependencies => FA.Proof_Dependencies,
            Tasking            => FA.Tasking,
            Generating_Globals => FA.Generating_Globals);

         Add_Vertex
           (FA,
            Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Var_Def    => Flatten_Variable (LP, FA.B_Scope),
               Var_Ex_Use => Vars,
               Subp_Calls => Funcalls,
               Indt_Calls => Indcalls,
               Vertex_Ctx => Ctx.Vertex_Ctx,
               E_Loc      => N),
            V);
         Ctx.Folded_Function_Checks.Append (LB);
         Ctx.Folded_Function_Checks.Append (HB);

         --  Work out which of the three variants (empty, full, unknown)
         --  we have... When an iterator filter is present, we consider
         --  the unknown case.

         --  We have an empty range. We should complain!

         if Is_Null_Range (LB, HB) then
            --  Flow goes into and out of the loop. Note that we do
            --  NOT hook up the loop body.
            CM (Union_Id (N)).Standard_Entry := V;
            CM (Union_Id (N)).Standard_Exits.Insert (V);

            Fully_Initialized := Flow_Id_Sets.Empty_Set;

         --  The loop is executed exactly once

         elsif Compile_Time_Compare (LB, HB, Assume_Valid => True) = EQ
           and then No (Filter)
         then
            --  Flow goes into loop declaration and out of the loop statements
            CM (Union_Id (N)).Standard_Entry := V;
            CM (Union_Id (N)).Standard_Exits.Union
              (CM (Union_Id (Statements (N))).Standard_Exits);

            --  Loop declaration is followed by the loop statements: V -> body
            Linkup (FA, V, CM (Union_Id (Statements (N))).Standard_Entry);

            Fully_Initialized := Variables_Initialized_By_Loop (N);

         --  We need to make sure the loop is executed at least once

         elsif Not_Null_Range (LB, HB) and then No (Filter) then
            --  Flow goes into the first statement and out the loop vertex
            CM (Union_Id (N)).Standard_Entry :=
              CM (Union_Id (Statements (N))).Standard_Entry;
            CM (Union_Id (N)).Standard_Exits.Insert (V);

            --  Loop the loop: V -> body -> V
            Linkup (FA, V, CM (Union_Id (Statements (N))).Standard_Entry);
            Linkup (FA, CM (Union_Id (Statements (N))).Standard_Exits, V);

            Fully_Initialized := Variables_Initialized_By_Loop (N);

         --  We don't know if the loop will be executed or not

         else
            --  Flow for the conditional for loop is like a while loop
            CM (Union_Id (N)).Standard_Entry := V;
            CM (Union_Id (N)).Standard_Exits.Insert (V);

            --  Loop the loop: V -> body -> V
            Linkup (FA, V, CM (Union_Id (Statements (N))).Standard_Entry);
            Linkup (FA, CM (Union_Id (Statements (N))).Standard_Exits, V);

            --  If an iterator filter is present, the detection of variables
            --  initialized by the loop is disabled.
            if Present (Filter) then
               Fully_Initialized := Flow_Id_Sets.Empty_Set;
            else
               Fully_Initialized := Variables_Initialized_By_Loop (N);
            end if;
         end if;

         Linkup_Continue_Statements (V);

         --  Set Potentially_Neverending_Vertex to the added vertex
         Potentially_Neverending_Vertex := V;
      end Do_For_Loop;

      ---------------------------
      -- Loop_Might_Exit_Early --
      ---------------------------

      function Loop_Might_Exit_Early (Loop_N : Node_Id) return Boolean is

         function Proc_Search (N : Node_Id) return Traverse_Result;

         -----------------
         -- Proc_Search --
         -----------------

         function Proc_Search (N : Node_Id) return Traverse_Result is
         begin
            case Nkind (N) is

               --  Those might cause the loop to exit early

               when N_Simple_Return_Statement
                  | N_Extended_Return_Statement
                  | N_Exit_Statement
                  | N_Goto_Statement
                  | N_Continue_Statement
               =>
                  return Abandon;

               --  In those the EXIT/RETURN statement, if present, will
               --  certainly refer to subprogram's own loop (EXIT) or to
               --  the suprogram itself (RETURN).

               when N_Subprogram_Body
                  | N_Subprogram_Declaration
                  | N_Package_Declaration
                  | N_Package_Body
                  | N_Generic_Declaration
               =>
                  return Skip;

               when others =>
                  return OK;
            end case;
         end Proc_Search;

         function Do_Search is new Traverse_More_Func (Proc_Search);
         --  Returns Abandon when Proc_Search returns it for any of the
         --  traversed nodes.

         --  Start of processing for Loop_Might_Exit_Early

      begin
         return Do_Search (Loop_N) = Abandon;
      end Loop_Might_Exit_Early;

      -----------------------------------
      -- Variables_Initialized_By_Loop --
      -----------------------------------

      function Variables_Initialized_By_Loop
        (Loop_N : Node_Id) return Flow_Id_Sets.Set
      is
         Fully_Initialized : Flow_Id_Sets.Set;

         type Target_Kind is (Precise, Imprecise, Invalid);

         type Target (Kind : Target_Kind := Invalid) is record
            case Kind is
               when Precise | Imprecise =>
                  Var : Flow_Id;
                  D   : Node_Lists.List;

               when Invalid =>
                  null;
            end case;
         end record;

         Null_Target : constant Target := (Kind => Invalid);

         Current_Loop : Node_Id := Types.Empty;
         Active_Loops : Node_Sets.Set := Node_Sets.Empty_Set;

         Lc : constant Graph_Connections :=
           CM (Union_Id (Statements (Loop_N)));
         --  A slice (represented by Standard_Entry and Standard_Exits) of the
         --  CFG for checking whether a variable is defined on all paths in
         --  the current loop.

         procedure Emit_Warning (T : Target; N : Node_Id);
         --  Emit warning about T being written in node N

         function Get_Array_Index (N : Node_Id) return Target
         with
           Pre  => Present (N),
           Post =>
             (if Get_Array_Index'Result.Kind = Precise
              then
                Get_Array_Index'Result.Var.Kind
                in Direct_Mapping | Record_Field
                and then not Get_Array_Index'Result.D.Is_Empty
                and then (for all E of Get_Array_Index'Result.D =>
                            Ekind (E) = E_Loop_Parameter));
         --  Convert the target of an assignment to an array into a flow id
         --  and a list of loop parameters.

         function Fully_Defined_In_Original_Loop (T : Target) return Boolean
         with Pre => T.Kind = Precise;
         --  Performs a mini-flow analysis on the current loop statements to
         --  see if T is defined on all paths (but not explicitly used).

         procedure Potentially_Defined (N : Node_Id)
         with Pre => Nkind (N) in N_Subexpr;
         --  Examine if a subexpression N denotes an component of an array that
         --  is fully initialized in the current loop.

         function Proc_Search (N : Node_Id) return Traverse_Result;
         --  In the traversal of the loop body, this finds suitable targets
         --  and checks if they are fully initialized.

         procedure Rec is new Traverse_More_Proc (Proc_Search);
         --  Wrapper around the traversal, so that Proc_Search can call itself

         ------------------
         -- Emit_Warning --
         ------------------

         procedure Emit_Warning (T : Target; N : Node_Id) is
            F   : Flow_Id renames T.Var;
            Obj : constant Entity_Id :=
              Get_Direct_Mapping_Id (Entire_Variable (F));
         begin
            if not Is_Default_Initialized (F)
              and then not (Present (Obj)
                            and then Ekind (Obj) = E_In_Out_Parameter)
              and then not Has_Relaxed_Initialization
                             (Get_Direct_Mapping_Id (F))
              and then not FA.Generating_Globals
            then
               if T.D.Length = 1 then
                  Warning_Msg_N (Warn_Init_Array, N);
               else
                  Warning_Msg_N (Warn_Init_Multidim_Array, N);
               end if;
            end if;
         end Emit_Warning;

         ---------------------
         -- Get_Array_Index --
         ---------------------

         function Get_Array_Index (N : Node_Id) return Target is
            F : Flow_Id;
            L : Node_Lists.List;

            Exact : Boolean := True;
            --  Assignment is considered exact until we find that it might not
            --  precisely represent an assigned array.

            Root : Node_Id;
            --  Used for descending into the root of the assigned object
            --  and then back when constructing the assigned target.

         begin
            --  First, is this really an array access?
            --  ??? We are not supporting array slices yet

            if Nkind (N) /= N_Indexed_Component then
               return Null_Target;
            end if;

            --  Does the Prefix chain only contain record fields?

            Root := Prefix (N);

            loop
               case Nkind (Root) is
                  when N_Identifier | N_Expanded_Name =>
                     exit;

                  when N_Selected_Component =>
                     Root := Prefix (Root);

                  when others =>
                     return Null_Target;
               end case;
            end loop;

            --  Construct the variable we're possibly fully defining

            loop
               case Nkind (Root) is
                  when N_Identifier | N_Expanded_Name =>

                     declare
                        E : constant Entity_Id := Entity (Root);
                     begin

                        --  Ignore objects declared within the loop itself

                        if In_Subtree (E, Loop_N) then
                           return Null_Target;
                        end if;

                        if Is_Protected_Component (E) then
                           F :=
                             Add_Component
                               (Direct_Mapping_Id (Sinfo.Nodes.Scope (E)), E);
                        elsif Is_Part_Of_Concurrent_Object (E) then
                           F :=
                             Add_Component
                               (Direct_Mapping_Id
                                  (Etype (Encapsulating_State (E))),
                                E);
                        else
                           F := Direct_Mapping_Id (E);
                        end if;
                     end;

                  when N_Selected_Component =>
                     F :=
                       Add_Component
                         (F, Unique_Component (Entity (Selector_Name (Root))));

                  when N_Indexed_Component =>
                     pragma Assert (Root = N);
                     exit;

                  when others =>
                     raise Program_Error;
               end case;

               Root := Parent (Root);
            end loop;

            --  Extract indices (and make sure they are simple and distinct)

            declare
               T : constant Entity_Id := Get_Type (Prefix (N), FA.B_Scope);

               Param_Expr  : Node_Id := First (Expressions (N)); --  LHS
               Index_Expr  : Node_Id := First_Index (T);         --  array
               Param_Range : Node_Id;
               Index_Range : Node_Id;

               Multi_Dim   : constant Boolean :=
                 List_Length (Expressions (N)) > 1;
               Current_Dim : Pos := 1;

               function Matches_Object_Bound
                 (Bound : Node_Id; Attr : Attribute_Id) return Boolean
               with
                 Pre =>
                   Nkind (Bound) in N_Subexpr
                   and then Attr in Attribute_First | Attribute_Last;
               --  Returns True iff the bound of the loop parameter's range
               --  ('First or 'Last) matches that same bound of the assigned
               --  array, e.g.:
               --
               --  for J in S'Range loop
               --     S (J) := ...;
               --  end loop;
               --
               --  Note: the 'Range in code like this will be expanded into
               --  'First or 'Last (depending on the value of Attr) and this
               --  is what we actually detect.

               --------------------------
               -- Matches_Object_Bound --
               --------------------------

               function Matches_Object_Bound
                 (Bound : Node_Id; Attr : Attribute_Id) return Boolean is
               begin
                  return
                    Nkind (Bound) = N_Attribute_Reference
                    and then Get_Attribute_Id (Attribute_Name (Bound)) = Attr
                    and then (if Nkind (Prefix (Bound))
                                 in N_Identifier | N_Expanded_Name
                              then Direct_Mapping_Id (Entity (Prefix (Bound)))
                              else Record_Field_Id (Prefix (Bound)))
                             = F
                    and then (if Multi_Dim
                              then
                                Intval (First (Expressions (Bound)))
                                = Current_Dim);
               end Matches_Object_Bound;

            begin
               while Present (Param_Expr) loop
                  case Nkind (Param_Expr) is
                     when N_Identifier | N_Expanded_Name =>
                        if L.Contains (Entity (Param_Expr)) then
                           --  Non-distinct entry, just abort. For
                           --  example:
                           --
                           --  for I in Idx loop
                           --     A (I, I) := 0;
                           --  end loop;
                           return Null_Target;
                        end if;

                        if not Active_Loops.Contains (Entity (Param_Expr)) then
                           --  Not a loop variable we care about, again
                           --  we just abort. For example:
                           --
                           --  for I in Idx loop
                           --     A (J) := 0;
                           --  end loop;
                           return Null_Target;
                        end if;

                        Param_Range := Get_Range (Entity (Param_Expr));
                        Index_Range := Get_Range (Index_Expr);

                        if (Compile_Time_Compare
                              (Low_Bound (Param_Range),
                               Low_Bound (Index_Range),
                               Assume_Valid => True)
                            = EQ
                            or else Matches_Object_Bound
                                      (Low_Bound (Param_Range),
                                       Attribute_First))
                          and then (Compile_Time_Compare
                                      (High_Bound (Param_Range),
                                       High_Bound (Index_Range),
                                       Assume_Valid => True)
                                    = EQ
                                    or else Matches_Object_Bound
                                              (High_Bound (Param_Range),
                                               Attribute_Last))
                        then
                           null;

                        --  The loop parameter type does not fully cover this
                        --  index type.

                        else
                           Exact := False;
                        end if;

                        L.Append (Entity (Param_Expr));

                     when others =>
                        --  This is not a simple entity, so just abort.
                        --  For example:
                        --
                        --  for I in Idx loop
                        --     A (I + 1) := 0;
                        --  end loop;

                        Exact := False;

                        L.Append (Param_Expr);
                  end case;

                  Next (Param_Expr);
                  Next_Index (Index_Expr);
                  Current_Dim := Current_Dim + 1;
               end loop;
            end;

            if Exact then
               return (Kind => Precise, Var => F, D => L);
            else
               return (Kind => Imprecise, Var => F, D => L);
            end if;
         end Get_Array_Index;

         ------------------------------------
         -- Fully_Defined_In_Original_Loop --
         ------------------------------------

         function Fully_Defined_In_Original_Loop (T : Target) return Boolean is
            Fully_Defined : Boolean := True;
            Touched       : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

            procedure Check_Defined
              (V  : Flow_Graphs.Vertex_Id;
               Tv : out Flow_Graphs.Simple_Traversal_Instruction);
            --  Visitor to ensure all paths define T (and do not use it)

            procedure Check_Unused
              (V  : Flow_Graphs.Vertex_Id;
               Tv : out Flow_Graphs.Simple_Traversal_Instruction);
            --  Visitor to ensure all paths following a definition of T do
            --  not use it.

            -------------------
            -- Check_Defined --
            -------------------

            procedure Check_Defined
              (V  : Flow_Graphs.Vertex_Id;
               Tv : out Flow_Graphs.Simple_Traversal_Instruction)
            is
               F : Flow_Id renames FA.CFG.Get_Key (V);
               A : V_Attributes renames FA.Atr (V);
            begin
               Touched.Insert (V);

               if A.Variables_Explicitly_Used.Contains (T.Var) then

                  Fully_Defined := False;
                  Tv := Flow_Graphs.Abort_Traversal;

               elsif A.Variables_Defined.Contains (T.Var)
                 and then F.Kind = Direct_Mapping
               then
                  declare
                     Var : constant Node_Id := Get_Direct_Mapping_Id (F);
                     pragma
                       Assert
                         (Nkind (Var) = N_Assignment_Statement
                            or else Is_Actual_Parameter (Var));
                     --  The written object is either assigned directly or via
                     --  an output of a subprogram call.

                     Var_Defined : constant Target :=
                       Get_Array_Index
                         (if Nkind (Var) = N_Assignment_Statement
                          then Name (Var)
                          else Var);

                  begin
                     if Var_Defined = T then
                        FA.CFG.DFS
                          (Start         => V,
                           Include_Start => False,
                           Visitor       => Check_Unused'Access);

                        if Fully_Defined then
                           Tv := Flow_Graphs.Skip_Children;
                        else
                           Tv := Flow_Graphs.Abort_Traversal;
                        end if;

                     --  ??? same as the enclosing ELSIF block; refactor

                     elsif Lc.Standard_Exits.Contains (V) then
                        Fully_Defined := False;
                        Tv := Flow_Graphs.Abort_Traversal;

                     else
                        Tv := Flow_Graphs.Continue;
                     end if;
                  end;

               elsif Lc.Standard_Exits.Contains (V) then
                  Fully_Defined := False;
                  Tv := Flow_Graphs.Abort_Traversal;

               else
                  Tv := Flow_Graphs.Continue;
               end if;
            end Check_Defined;

            ------------------
            -- Check_Unused --
            ------------------

            procedure Check_Unused
              (V  : Flow_Graphs.Vertex_Id;
               Tv : out Flow_Graphs.Simple_Traversal_Instruction) is
            begin
               if Touched.Contains (V) then
                  Tv := Flow_Graphs.Skip_Children;
               elsif FA.Atr (V).Variables_Explicitly_Used.Contains (T.Var) then

                  Fully_Defined := False;
                  Tv := Flow_Graphs.Abort_Traversal;

               else
                  Tv := Flow_Graphs.Continue;
               end if;
            end Check_Unused;

            --  Start of processing for Fully_Defined_In_Original_Loop

         begin
            FA.CFG.DFS
              (Start         => Lc.Standard_Entry,
               Include_Start => True,
               Visitor       => Check_Defined'Access);

            return Fully_Defined;
         end Fully_Defined_In_Original_Loop;

         -------------------------
         -- Potentially_Defined --
         -------------------------

         procedure Potentially_Defined (N : Node_Id) is
            T : constant Target := Get_Array_Index (N);
         begin
            case T.Kind is
               when Precise =>
                  if Fully_Defined_In_Original_Loop (T) then
                     Fully_Initialized.Include (T.Var);
                  else
                     Emit_Warning (T, N);
                  end if;

               when Imprecise =>
                  Emit_Warning (T, N);

               when Invalid =>
                  null;
            end case;
         end Potentially_Defined;

         -----------------
         -- Proc_Search --
         -----------------

         function Proc_Search (N : Node_Id) return Traverse_Result is
         begin
            case Nkind (N) is
               when N_Loop_Statement =>
                  if N = Current_Loop then
                     return OK;

                  elsif Is_For_Loop (N) then
                     declare
                        Old_Loop      : constant Node_Id := Current_Loop;
                        Loop_Variable : constant Entity_Id :=
                          Get_Loop_Variable (N);

                     begin
                        Current_Loop := N;
                        Active_Loops.Insert (Loop_Variable);

                        Rec (N);

                        Current_Loop := Old_Loop;
                        Active_Loops.Delete (Loop_Variable);
                     end;

                     return Skip;
                  end if;

               when N_Assignment_Statement =>
                  Potentially_Defined (Name (N));

               when N_Procedure_Call_Statement | N_Entry_Call_Statement =>
                  declare
                     procedure Handle_Parameter
                       (Formal : Entity_Id; Actual : Node_Id);

                     ----------------------
                     -- Handle_Parameter --
                     ----------------------

                     procedure Handle_Parameter
                       (Formal : Entity_Id; Actual : Node_Id) is
                     begin
                        if Ekind (Formal) = E_Out_Parameter then
                           Potentially_Defined (Actual);
                        end if;
                     end Handle_Parameter;

                     procedure Handle_Parameters is new
                       Iterate_Call_Parameters
                         (Handle_Parameter => Handle_Parameter);

                  begin
                     Handle_Parameters (N);
                  end;

               --  Don't traverse into subprograms (because we don't check if
               --  they are executed) and into packages (because they can only
               --  modify their own objects anyway).

               when N_Subprogram_Body
                  | N_Subprogram_Declaration
                  | N_Package_Declaration
                  | N_Package_Body
                  | N_Generic_Declaration
               =>
                  return Skip;

               when others =>
                  null;
            end case;
            return OK;
         end Proc_Search;

         --  Start of processing for Variables_Initialized_By_Loop

      begin
         if Loop_Might_Exit_Early (Loop_N) then
            return Flow_Id_Sets.Empty_Set;
         end if;

         Rec (Loop_N);

         return Fully_Initialized;
      end Variables_Initialized_By_Loop;

      ----------------------
      -- Do_Iterator_Loop --
      ----------------------

      procedure Do_Iterator_Loop is
         I_Spec : constant Node_Id :=
           Iterator_Specification (Iteration_Scheme (N));

         Param  : constant Entity_Id := Defining_Identifier (I_Spec);
         Cont   : constant Node_Id := Name (I_Spec);
         Filter : constant Node_Id := Iterator_Filter (I_Spec);

         V        : Flow_Graphs.Vertex_Id;
         Funcalls : Call_Sets.Set;
         Indcalls : Node_Sets.Set;
      begin
         --  Set up parameter variable
         Create_Initial_And_Final_Vertices (Param, FA);

         --  Create vertex for the container expression. We also define the
         --  loop parameter here.
         Pick_Generated_Info
           (I_Spec,
            FA.B_Scope,
            Function_Calls     => Funcalls,
            Indirect_Calls     => Indcalls,
            Proof_Dependencies => FA.Proof_Dependencies,
            Tasking            => FA.Tasking,
            Generating_Globals => FA.Generating_Globals);

         Add_Vertex
           (FA,
            Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Var_Def    => Flatten_Variable (Param, FA.B_Scope),
               Var_Ex_Use =>
                 Get_Variables
                   (Cont,
                    Scope                => FA.B_Scope,
                    Target_Name          => Null_Flow_Id,
                    Fold_Functions       => Inputs,
                    Use_Computed_Globals => not FA.Generating_Globals)
                 or Get_Filter_Variables (Filter),
               Subp_Calls => Funcalls,
               Indt_Calls => Indcalls,
               Vertex_Ctx => Ctx.Vertex_Ctx,
               E_Loc      => Cont),
            V);
         Ctx.Folded_Function_Checks.Append (Cont);

         --  Pretty normal flow (see while loops)
         CM (Union_Id (N)).Standard_Entry := V;
         CM (Union_Id (N)).Standard_Exits.Insert (V);

         --  Loop the loop: V -> body -> V
         Linkup (FA, V, CM (Union_Id (Statements (N))).Standard_Entry);
         Linkup (FA, CM (Union_Id (Statements (N))).Standard_Exits, V);

         Linkup_Continue_Statements (V);

         --  Set Potentially_Neverending_Vertex to the added vertex
         Potentially_Neverending_Vertex := V;
      end Do_Iterator_Loop;

      I_Scheme          : constant Node_Id := Iteration_Scheme (N);
      Loop_Id           : constant Entity_Id := Entity (Identifier (N));
      Fully_Initialized : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      Loop_Writes       : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      Outer_Termination : constant Boolean := Ctx.Termination_Proved;

      --  Start of processing for Do_Loop_Statement

   begin
      --  Start with a blank slate for the loops entry and exit
      CM.Insert (Union_Id (N), No_Connections);

      --  Construct graph for the loop body. Please note that early
      --  exits may already change the above, so be sure to only use
      --  union or include, instead of setting the standard exits.
      --
      --  We also change the context to include the current
      --  loop. Please note that we don't flag the loop statement
      --  itself as part of the loop, hence the corresponding delete
      --  is here as well.
      Ctx.Vertex_Ctx.Current_Loops.Insert (Loop_Id);
      Ctx.Entry_References.Insert (Loop_Id, Node_Sets.Empty_Set);
      Ctx.Termination_Proved := False;

      declare
         Outer_Loop : constant Entity_Id := Ctx.Active_Loop;
      begin
         --  We can't use 'Update here as we may modify Ctx
         Ctx.Active_Loop := Loop_Id;
         Process_Statement_List (Statements (N), FA, CM, Ctx);
         Ctx.Active_Loop := Outer_Loop;
      end;

      --  Collect loop writes, this is needed to determine if the root object
      --  of a path expression in the iteration scheme is modified during the
      --  loop.

      if not FA.Generating_Globals then
         for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
            declare
               Atr : V_Attributes renames FA.Atr (V);

            begin
               if Atr.Loops.Contains (Loop_Id)
                 and then not Atr.In_Nested_Package
               then
                  for Var of Atr.Variables_Defined.Union (Atr.Volatiles_Read)
                  loop
                     if not Synthetic (Var) then
                        Loop_Writes.Include
                          (Change_Variant (Entire_Variable (Var), Normal_Use));
                     end if;
                  end loop;
               end if;
            end;
         end loop;
      end if;

      Ctx.Termination_Proved :=
        Ctx.Termination_Proved
        or else Termination_Proved
                  (I_Scheme, Loop_Writes, FA.Generating_Globals);

      if No (I_Scheme) then
         --  We have a general (possibly infinite) loop
         Do_Loop;

      elsif Present (Condition (I_Scheme)) then
         --  We have a while loop
         Do_While_Loop;

      elsif Present (Loop_Parameter_Specification (I_Scheme)) then
         --  This is a normal for loop over a type or range
         Do_For_Loop (Fully_Initialized);

         if not FA.Generating_Globals then
            Loop_Writes.Insert
              (Direct_Mapping_Id
                 (Defining_Identifier
                    (Loop_Parameter_Specification (I_Scheme))));

            --  Sanity checking: Fully_Initialized variables are a subset of
            --  all loop writes. This is not checked in phase 1 as Loop_Writes
            --  is empty.
            pragma
              Assert
                (To_Entire_Variables (Fully_Initialized).Is_Subset
                   (Of_Set => Loop_Writes));
         end if;

      elsif Present (Iterator_Specification (I_Scheme)) then
         --  This is a `in' or `of' loop over some container
         Do_Iterator_Loop;

         if not FA.Generating_Globals then
            Loop_Writes.Insert
              (Direct_Mapping_Id
                 (Defining_Identifier (Iterator_Specification (I_Scheme))));
         end if;

      else
         raise Program_Error;
      end if;

      CM.Delete (Union_Id (Statements (N)));

      --  Check whether the non-terminating loop is immediately in the analysed
      --  unit (and not in the package body statements of a nested package,
      --  which will be handled as a subprogram call).

      if Enclosing_Unit (Loop_Id) = FA.Spec_Entity
        and then not Ctx.Termination_Proved
      then
         FA.Has_Only_Terminating_Constructs := False;
         FA.Atr (Potentially_Neverending_Vertex).Is_Neverending := True;
      end if;

      --  If we need an init vertex, we add it before the loop itself
      if not Fully_Initialized.Is_Empty then
         declare
            V : Flow_Graphs.Vertex_Id;
         begin
            Add_Vertex
              (FA,
               (Make_Basic_Attributes
                  (Var_Def    => Fully_Initialized,
                   Vertex_Ctx => Ctx.Vertex_Ctx,
                   E_Loc      => Loop_Id,
                   Print_Hint => Pretty_Print_Loop_Init)
                with delta Is_Program_Node => False),
               V);

            Linkup (FA, V, CM (Union_Id (N)).Standard_Entry);
            CM (Union_Id (N)).Standard_Entry := V;
         end;
      end if;

      --  Now we need to glue the 'Loop_Entry checks to the front of the loop
      declare
         Augmented_Loop : Union_Lists.List := Union_Lists.Empty_List;
         V              : Flow_Graphs.Vertex_Id;
         Block          : Graph_Connections;
      begin
         --  We stick all loop entry references on a list of nodes
         for Reference of Ctx.Entry_References (Loop_Id) loop
            Add_Vertex
              (FA,
               Direct_Mapping_Id (Reference),
               Make_Sink_Vertex_Attributes
                 (Var_Use       =>
                    Get_All_Variables
                      (Prefix (Reference),
                       Scope                => FA.B_Scope,
                       Target_Name          => Null_Flow_Id,
                       Use_Computed_Globals => not FA.Generating_Globals),
                  Is_Assertion  => True,
                  Is_Loop_Entry => True,
                  Vertex_Ctx    => Ctx.Vertex_Ctx),
               V);
            Ctx.Folded_Function_Checks.Append (Prefix (Reference));

            CM.Insert (Union_Id (Reference), Trivial_Connection (V));

            Augmented_Loop.Append (Union_Id (Reference));
         end loop;

         --  Then we stick the actual loop at the end
         Augmented_Loop.Append (Union_Id (N));

         --  Connect up the dots, and finally re-insert the connection to the
         --  block with 'Loop_Entry checks.
         Join (FA => FA, CM => CM, Nodes => Augmented_Loop, Block => Block);
         CM.Insert (Union_Id (N), Block);
      end;

      Ctx.Entry_References.Delete (Loop_Id);
      Ctx.Vertex_Ctx.Current_Loops.Delete (Loop_Id);
      Ctx.Termination_Proved := Outer_Termination;

      --  Finally, we can update the loop information in Flow_Utility for proof

      if not FA.Generating_Globals then
         Add_Loop_Writes (Loop_Id, Expand_Abstract_States (Loop_Writes));
      end if;
   end Do_Loop_Statement;

   -----------------------
   -- Do_Null_Statement --
   -----------------------

   procedure Do_Null_Statement
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
           (E_Loc => N, Execution => Normal_Execution),
         V);
      CM.Insert (Union_Id (N), Trivial_Connection (V));
   end Do_Null_Statement;

   ---------------------------
   -- Do_Object_Declaration --
   ---------------------------

   procedure Do_Object_Declaration
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V     : Flow_Graphs.Vertex_Id;
      Inits : Vertex_Lists.List;

      E : constant Entity_Id := Defining_Identifier (N);
      --  Entity of the object declared by node N

      Typ : constant Entity_Id := Etype (E);

      Expr : constant Node_Id := Expression (N);
      --  Object's initialization expression

      subtype Size_Type is Int range -1 .. Int'Last;
      --  Used for size of an array type. -1 stands for many components, in
      --  case we are not able to determine the exact number.

      procedure Find_Tasks (T : Entity_Id; Size : Size_Type)
      with Pre => Is_Type (T);
      --  Update the map with number of task instances.
      --
      --  It checks which and how many tasks are instantiated when an object of
      --  type T is declared. Flag Array_Component should be True if the parent
      --  type is an array with possibly more than one element.
      --
      --  This procedure mirrors Count_Tasks from
      --  Sem_Ch3.Analyze_Object_Declaration.

      procedure Add_Vertex_For_DIC
        (Default_Init_Param : Entity_Id; Default_Init_Expr : Node_Id)
      with
        Pre =>
          Ekind (Default_Init_Param) = E_In_Parameter
          and then Nkind (Default_Init_Expr) in N_Subexpr;
      --  Add a sink vertex for a Default_Initial_Condition aspect.
      --  Default_Init_Param is the entity for the current type instance and
      --  Default_Init_Expr is the expression of the DIC.

      function Constraint (T : Entity_Id; D : Entity_Id) return Node_Id
      with
        Pre  => Has_Discriminants (T) and then Ekind (D) = E_Discriminant,
        Post => Nkind (Constraint'Result) in N_Subexpr;
      --  Returns constraint expression of type T for its discriminant D
      --
      --  ??? It duplicates SPARK_Util.Types.Get_Constraint_For_Discr, except
      --  for a use of Unique_Component, which is needed because D is taken
      --  from a Flow_Id, where it was processed with Unique_Component.

      function Component_Less (Left, Right : Flow_Id) return Boolean
      with
        Pre =>
          Left.Kind in Direct_Mapping | Record_Field
          and then Right.Kind in Direct_Mapping | Record_Field
          and then Left.Variant = Normal_Use
          and then Right.Variant = Normal_Use
          and then Left.Node = Right.Node;
      --  Ordering function for sorting. See Sort_Discriminants_First.

      --------------------
      -- Component_Less --
      --------------------

      function Component_Less (Left, Right : Flow_Id) return Boolean is
         Discr_Left  : constant Boolean := Is_Discriminant (Left);
         Discr_Right : constant Boolean := Is_Discriminant (Right);
      begin
         if Discr_Left and Discr_Right then
            if Left.Component.Length = Right.Component.Length then
               return Left < Right;
            else
               return Left.Component.Length < Right.Component.Length;
            end if;
         elsif Discr_Left xor Discr_Right then
            return Discr_Left;
         else
            return Left < Right;
         end if;
      end Component_Less;

      package Component_Lists is new
        Ada.Containers.Doubly_Linked_Lists (Element_Type => Flow_Id);

      package Component_Sorting is new
        Component_Lists.Generic_Sorting ("<" => Component_Less);

      function Sort_Discriminants_First
        (Components : Flow_Id_Sets.Set) return Component_Lists.List
      with
        Post => Component_Sorting.Is_Sorted (Sort_Discriminants_First'Result);
      --  Sorting function. Sorts a Flow Id set into a list such that outer
      --  record discriminants come before inner discriminants, then the other
      --  variables come last.

      ------------------------------
      -- Sort_Discriminants_First --
      ------------------------------

      function Sort_Discriminants_First
        (Components : Flow_Id_Sets.Set) return Component_Lists.List
      is
         Sorted : Component_Lists.List;
      begin
         for Component of Components loop
            Sorted.Append (Component);
         end loop;

         Component_Sorting.Sort (Sorted);

         return Sorted;
      end Sort_Discriminants_First;

      ----------------
      -- Find_Tasks --
      ----------------

      procedure Find_Tasks (T : Entity_Id; Size : Size_Type) is

         function Number_Elements return Size_Type
         with Pre => Is_Array_Type (T);
         --  Returns the number of elements in the array type T

         ---------------------
         -- Number_Elements --
         ---------------------

         function Number_Elements return Size_Type is
            C : Entity_Id;
            X : Node_Id := First_Index (T);

            S : Size_Type := 1;
            --  Number of elements in the array
         begin
            --  Check whether the array is empty (at least one index range
            --  statically equal zero) or has exectly one component (all ranges
            --  statically equal one); otherwise assume it has many components.

            while Present (X) loop
               C := Etype (X);

               if not Is_OK_Static_Subtype (C) then
                  --  In case we are not able to determine the exact size, we
                  --  set S to -1, giving it the meaning of many.
                  S := -1;
               else
                  declare
                     Length : constant Uint :=
                       (UI_Max
                          (Uint_0,
                           Expr_Value (Type_High_Bound (C))
                           - Expr_Value (Type_Low_Bound (C))
                           + Uint_1));

                  begin
                     if Length = 0 then
                        S := 0;
                        exit;
                     else
                        if S = -1 then
                           null;
                        else
                           S := S * UI_To_Int (Length);
                        end if;
                     end if;
                  end;
               end if;

               Next_Index (X);
            end loop;

            return S;
         end Number_Elements;

         --  Start of processing for Find_Tasks

      begin
         if not Has_Task (T) and then not Has_Protected (T) then
            return;

         elsif Is_Task_Type (T) then
            --  For discriminated tasks record the number of instances of
            --  the base type.
            GG_Register_Task_Object
              (Typ       => Etype (T),
               Object    => E,
               Instances => (if Size > 1 or else Size = -1 then Size else 1));

         --  Attached interrupt handlers can be executed spontaneously, just
         --  like task types, so we treat them in the same way.

         elsif Is_Protected_Type (T) and then Has_Attach_Handler (T) then
            declare
               Prot_E : Entity_Id := First_Entity (T);
               --  Iterator for entities of the protected object (including
               --  protected components, but they are easy to ignore).
               --
               --  Note: unlike for derived types and subtypes of task types,
               --  for protected types we don't need to look into the base
               --  type, because by calling First_Entity/Next_Entity we
               --  effectively iterate over the base type.

            begin
               while Present (Prot_E) loop
                  --  The Ravenscar profile forbids the use of pragma
                  --  Interrupt_Handler, so Is_Interrupt_Handler is equivalent
                  --  to checking if pragma Attach_Handler is present (but
                  --  slightly cheaper).

                  if Ekind (Prot_E) = E_Procedure
                    and then Entity_In_SPARK (Prot_E)
                    and then Is_Interrupt_Handler (Prot_E)
                  then
                     GG_Register_Task_Object
                       (Typ       => Prot_E,
                        Object    => E,
                        Instances =>
                          (if Size > 1 or else Size = -1 then Size else 1));
                  end if;
                  Next_Entity (Prot_E);
               end loop;
            end;

         elsif Is_Record_Type (T) then
            declare
               C : Entity_Id := First_Component (T);
               --  Iterator for record components. We do not assume any
               --  particular values of discriminants and thus ignore how the
               --  record is split into variants; instead, we conservatively
               --  detect all tasks.

            begin
               while Present (C) loop
                  Find_Tasks (Etype (C), Size);
                  Next_Component (C);
               end loop;
            end;

         elsif Is_Array_Type (T) then
            declare
               S : constant Size_Type := Number_Elements;

            begin
               if S /= 0 then
                  Find_Tasks (Component_Type (T), Size => S);
               end if;
            end;
         end if;
      end Find_Tasks;

      ------------------------
      -- Add_Vertex_For_DIC --
      ------------------------

      procedure Add_Vertex_For_DIC
        (Default_Init_Param : Entity_Id; Default_Init_Expr : Node_Id)
      is
         Funcalls       : Call_Sets.Set;
         Indcalls       : Node_Sets.Set;
         Variables_Used : Flow_Id_Sets.Set;

         DIC_Param_Components : constant Flow_Id_Sets.Set :=
           Flatten_Variable (Default_Init_Param, FA.B_Scope);
         --  Flattened view of the DIC procedure parameter

      begin
         --  Default initial condition can refer to the type mark, e.g.:
         --
         --     type T is private
         --       with Default_Initial_Condition => Foo (T) > 2;
         --
         --  and the frontend will wrap the DIC expression inside a procedure:
         --
         --      procedure TDefault_Initial_Condition (_object : T) is
         --      begin
         --         pragma Check
         --           (Default_Initial_Condition,
         --            Foo (_object) > 2);
         --      end TDefault_Initial_Condition;
         --
         --  When an object of that type is later declared like:
         --
         --     X : T;
         --
         --  we "inline" a call to this procedure by creating a single
         --  assertion vertex with references to _object in the pragma Check
         --  expression replaced with references to X.
         --
         --  However, instead of replacing individual references to _object
         --  components, we check if any of the components is referenced. If it
         --  is, we simply remove all references to _object components and add
         --  refences to all components of X.
         --
         --  This is closer to what really happens when the DIC procedure is
         --  called and also nicely supports an otherwise complicated scenario
         --  when a DIC procedure that takes a parameter of an unconstrained
         --  type is called with an object of a constrained type. (In this
         --  scenario the DIC expression might refer to components of the
         --  _object parameter that are not present in the declared object.)

         Variables_Used :=
           Get_Variables
             (Default_Init_Expr,
              Scope                => FA.B_Scope,
              Target_Name          => Null_Flow_Id,
              Fold_Functions       => Inputs,
              Use_Computed_Globals => not FA.Generating_Globals);

         --  Replace components if needed
         if (for some Comp of DIC_Param_Components =>
               Variables_Used.Contains (Comp))
         then
            Variables_Used.Difference (DIC_Param_Components);
            Variables_Used.Union (Flatten_Variable (E, FA.B_Scope));
         end if;

         Pick_Generated_Info
           (Default_Init_Expr,
            FA.B_Scope,
            Function_Calls     => Funcalls,
            Indirect_Calls     => Indcalls,
            Proof_Dependencies => FA.Proof_Dependencies,
            Tasking            => FA.Tasking,
            Generating_Globals => FA.Generating_Globals);

         Add_Vertex
           (FA,
            Make_Sink_Vertex_Attributes
              (Var_Use      => Variables_Used,
               Subp_Calls   => Funcalls,
               Indt_Calls   => Indcalls,
               Is_Assertion => True,
               Vertex_Ctx   => Ctx.Vertex_Ctx,
               Aspect       => DIC,
               E_Loc        => N),
            V);
         Inits.Append (V);

         --  Check for folded functions
         Ctx.Folded_Function_Checks.Append (Default_Init_Expr);
      end Add_Vertex_For_DIC;

      ----------------
      -- Constraint --
      ----------------

      function Constraint (T : Entity_Id; D : Entity_Id) return Node_Id is
         Current : Entity_Id := First_Discriminant (T);
         Elmt    : Elmt_Id := First_Elmt (Discriminant_Constraint (T));
      begin
         while Unique_Component (Current) /= D loop
            Next_Discriminant (Current);
            Next_Elmt (Elmt);
         end loop;
         return Node (Elmt);
      end Constraint;

      --  Local variables

      Alias : constant Entity_Id := Ultimate_Overlaid_Entity (E);

      --  Start of processing for Do_Object_Declaration

   begin
      --  Task creation and activation in a protected action are potentially
      --  blocking, but in SPARK task types are only allowed when the Ravenscar
      --  profile is active and in the Ravenscar task objects are only allowed
      --  at the library level.
      pragma
        Assert
          (if FA.Generating_Globals and then Has_Task (Etype (E))
             then Is_Library_Level_Entity (E));

      --  Ignore generic actuals of the currently analysed instance.
      --
      --  Inside of generic instance they act as globals, i.e. they shall
      --  appear in the [generated] Global and Initializes. We introduce them
      --  when processing those contracts, not when processing the declarations
      --  in the generic instance.
      --
      --  Outside of generic instance they are simply not visible, so we also
      --  do not introduce vertices for them.

      if In_Generic_Actual (E) then
         Add_Dummy_Vertex (N, FA, CM);
         return;
      end if;

      --  For Part_Of concurrent objects we only want them in the CFG if they
      --  are declared immediately within the analysed package; otherwise they
      --  cannot be referenced.

      if Is_Part_Of_Concurrent_Object (E) and then Scope (E) /= FA.Spec_Entity
      then
         Add_Dummy_Vertex (N, FA, CM);
         return;
      end if;

      case Ekind (E) is
         when E_Constant =>
            if Present (Alias) then
               pragma Assert (Is_Imported (E) and then No (Expr));

            elsif Present (Expr) then
               --  Completion of a deferred constant

               if Is_Full_View (E) then
                  null;

               --  Ordinary constant with an initialization expression

               else
                  Register_Own_Variable (FA, E);
                  Create_Initial_And_Final_Vertices (E, FA);
               end if;

            else
               --  Declaration of a deferred constant

               if Present (Full_View (E)) then
                  Register_Own_Variable (FA, Full_View (E));
                  Create_Initial_And_Final_Vertices (Full_View (E), FA);

                  Add_Dummy_Vertex (N, FA, CM);
                  return;

               --  Imported constant

               else
                  pragma Assert (Is_Imported (E));
                  Register_Own_Variable (FA, E);
                  Create_Initial_And_Final_Vertices (E, FA);

               end if;
            end if;

         when E_Variable =>
            if No (Alias) then
               Register_Own_Variable (FA, E);
               Create_Initial_And_Final_Vertices (E, FA);
            end if;

         when others =>
            raise Program_Error;
      end case;

      --  We pull proof dependencies from the type of the object. Type
      --  invariants are pulled in the enclosing unit only when the object
      --  has no initialization, or it is a library-level entity.
      Process_Type_Contracts
        (Etype (E),
         FA.B_Scope,
         No (Expr) or else Is_Library_Level_Entity (E),
         FA.Proof_Dependencies);

      --  Declaration with a function that has side effects is handled like a
      --  subprogram call: the function entity acts like a formal parameter of
      --  mode OUT and the defining identifier acts like the corresponding
      --  actual parameter.

      if Present (Expr)
        and then Nkind (Expr) = N_Function_Call
        and then Is_Function_With_Side_Effects (Get_Called_Entity (Expr))
      then
         Do_Call_Statement (Expr, FA, CM, Ctx);
         Move_Connections (CM, Dst => Union_Id (N), Src => Union_Id (Expr));
         return;
      end if;

      --  We have a declaration with an explicit initialization

      if Present (Expr) then
         declare
            Funcalls : Call_Sets.Set;
            Indcalls : Node_Sets.Set;

            To_CW : constant Boolean :=
              Is_Class_Wide_Type (Get_Type (E, FA.B_Scope))
              and then not Is_Class_Wide_Type (Get_Type (Expr, FA.B_Scope));

            Var_Def : constant Flow_Id_Sets.Set :=
              (if Present (Alias)
               then Flatten_Variable (Alias, FA.B_Scope)
               else Flatten_Variable (E, FA.B_Scope));

         begin
            Pick_Generated_Info
              (Expr,
               FA.B_Scope,
               Function_Calls     => Funcalls,
               Indirect_Calls     => Indcalls,
               Proof_Dependencies => FA.Proof_Dependencies,
               Tasking            => FA.Tasking,
               Generating_Globals => FA.Generating_Globals);

            if No (Alias) and then RHS_Split_Useful (E, Expr, FA.B_Scope) then

               declare
                  M : constant Flow_Id_Maps.Map :=
                    Untangle_Record_Assignment
                      (N                       => Expr,
                       Map_Root                => Direct_Mapping_Id (E),
                       Map_Type                => Get_Type (E, FA.B_Scope),
                       Target_Name             => Null_Flow_Id,
                       Scope                   => FA.B_Scope,
                       Fold_Functions          => Inputs,
                       Use_Computed_Globals    => not FA.Generating_Globals,
                       Expand_Internal_Objects => False,
                       Extensions_Irrelevant   =>
                         not Is_Class_Wide_Type (Get_Type (E, FA.B_Scope)));

                  Cluster : Flow_Graphs.Cluster_Id;
                  --  For grouping vertices corresponding to this object
                  --  declaration in the visual representation of the graph.

                  Empty_Reuse : Flow_Graphs.Vertex_Id :=
                    Flow_Graphs.Null_Vertex;

               begin
                  FA.CFG.New_Cluster (Cluster);

                  for C in M.Iterate loop
                     declare
                        Output : Flow_Id renames Flow_Id_Maps.Key (C);
                        Inputs : Flow_Id_Sets.Set renames M (C);

                     begin
                        --  ??? It might be useful to improve E_Loc to point
                        --      at the relevant bit in the aggregate.

                        if Inputs.Is_Empty then
                           if Empty_Reuse = Flow_Graphs.Null_Vertex then
                              Add_Vertex
                                (FA,
                                 (Make_Basic_Attributes
                                    (Var_Def    => Flow_Id_Sets.Empty_Set,
                                     Var_Ex_Use => Inputs,
                                     Subp_Calls => Funcalls,
                                     Indt_Calls => Indcalls,
                                     Vertex_Ctx => Ctx.Vertex_Ctx,
                                     E_Loc      => N,
                                     Print_Hint => Pretty_Print_Record_Field)
                                  with delta Is_Declaration_Node => True),
                                 V);

                              Inits.Append (V);
                              FA.Atr (V).First_Field := Inits.First_Element;
                              FA.CFG.Set_Cluster (V, Cluster);

                              Empty_Reuse := V;
                           end if;

                           FA.Atr (Empty_Reuse).Variables_Defined.Insert
                             (Output);
                        else
                           Add_Vertex
                             (FA,
                              (Make_Basic_Attributes
                                 (Var_Def    => Flow_Id_Sets.To_Set (Output),
                                  Var_Ex_Use => Inputs,
                                  Subp_Calls => Funcalls,
                                  Indt_Calls => Indcalls,
                                  Vertex_Ctx => Ctx.Vertex_Ctx,
                                  E_Loc      => N,
                                  Print_Hint => Pretty_Print_Record_Field)
                               with delta Is_Declaration_Node => True),
                              V);

                           Inits.Append (V);
                           FA.Atr (V).First_Field := Inits.First_Element;
                           FA.CFG.Set_Cluster (V, Cluster);
                        end if;
                     end;
                  end loop;
               end;

            else
               Add_Vertex
                 (FA,
                  Direct_Mapping_Id (N),
                  (Make_Basic_Attributes
                     (Var_Def    => Var_Def,
                      Var_Ex_Use =>
                        Get_Variables
                          (Expr,
                           Scope                => FA.B_Scope,
                           Target_Name          => Null_Flow_Id,
                           Fold_Functions       => Inputs,
                           Use_Computed_Globals => not FA.Generating_Globals,
                           Consider_Extensions  => To_CW),
                      Subp_Calls => Funcalls,
                      Indt_Calls => Indcalls,
                      Vertex_Ctx => Ctx.Vertex_Ctx,
                      E_Loc      => N)
                   with delta Is_Declaration_Node => True),
                  V);
               Inits.Append (V);

               --  If this object is a local borrower, then put its declaration
               --  on the stack. We only need this for assignments whose RHS
               --  doesn't need to be split, because local borrowers are always
               --  of an access type and thus in flow they are represented as
               --  single "blobs".

               if Is_Anonymous_Access_Object_Type (Get_Type (E, FA.B_Scope))
                 and then not Is_Access_Constant (Get_Type (E, FA.B_Scope))
               then
                  Ctx.Borrowers.Append (N);
               end if;

            end if;

            Ctx.Folded_Function_Checks.Append (Expr);
         end;
         pragma Assert (not Inits.Is_Empty);

      --  We have a non-overlaid object with Import and Address clause

      elsif Is_Imported (E)
        and then No (Alias)
        and then Present (Address_Clause (E))
      then
         declare
            Addr_Expr : constant N_Subexpr_Id :=
              Expression (Address_Clause (E));
            Addr_Deps : constant Flow_Id_Sets.Set :=
              Get_Variables
                (Addr_Expr,
                 Scope                => FA.B_Scope,
                 Target_Name          => Null_Flow_Id,
                 Fold_Functions       => Inputs,
                 Use_Computed_Globals => not FA.Generating_Globals);
            Funcalls  : Call_Sets.Set;
            Indcalls  : Node_Sets.Set;

         begin
            Pick_Generated_Info
              (Addr_Expr,
               Scop               => FA.B_Scope,
               Function_Calls     => Funcalls,
               Indirect_Calls     => Indcalls,
               Proof_Dependencies => FA.Proof_Dependencies,
               Tasking            => FA.Tasking,
               Generating_Globals => FA.Generating_Globals);

            for F of Flatten_Variable (E, FA.B_Scope) loop
               Add_Vertex
                 (FA,
                  Make_Basic_Attributes
                    (Var_Def    => Flow_Id_Sets.To_Set (F),
                     Var_Ex_Use => Addr_Deps,
                     Subp_Calls => Funcalls,
                     Indt_Calls => Indcalls,
                     Vertex_Ctx => Ctx.Vertex_Ctx,
                     Print_Hint => Pretty_Print_Record_Field,
                     E_Loc      => Addr_Expr),
                  V);
               Inits.Append (V);
            end loop;

            Ctx.Folded_Function_Checks.Append (Addr_Expr);
         end;

      --  We have no initializing expression so we fall back to the default
      --  initialization (if any).

      else
         for F of
           Sort_Discriminants_First
             (Flatten_Variable
                ((if Present (Alias) then Alias else E), FA.B_Scope))
         loop
            if Is_Discriminant (F) then
               declare
                  Composite : constant Entity_Id :=
                    Etype
                      (if F.Component.Length = 1
                       then Get_Direct_Mapping_Id (F)
                       else F.Component (F.Component.Last_Index - 1));
                  --  Composite type discriminated by F. We must use the type
                  --  of the constrained composite object and not simply the
                  --  scope of the discriminant.

                  Full_Composite : constant Entity_Id :=
                    (if Present (Full_View (Composite))
                     then Full_View (Composite)
                     else Composite);
                  --  Full view of the composite type

                  Constraint_Expr : constant Node_Id :=
                    Constraint
                      (T => Full_Composite, D => F.Component.Last_Element);
                  --  Constraint expression that initializes discriminant F

                  Constraint_Vars : constant Flow_Id_Sets.Set :=
                    Get_Variables
                      (Constraint_Expr,
                       Scope                => FA.B_Scope,
                       Target_Name          => Null_Flow_Id,
                       Fold_Functions       => Inputs,
                       Use_Computed_Globals => not FA.Generating_Globals);

                  Funcalls : Call_Sets.Set;
                  Indcalls : Node_Sets.Set;

               begin
                  Pick_Generated_Info
                    (Constraint_Expr,
                     Scop               => FA.B_Scope,
                     Function_Calls     => Funcalls,
                     Indirect_Calls     => Indcalls,
                     Proof_Dependencies => FA.Proof_Dependencies,
                     Tasking            => FA.Tasking,
                     Generating_Globals => FA.Generating_Globals);

                  Add_Vertex
                    (FA,
                     Make_Basic_Attributes
                       (Var_Def    => Flow_Id_Sets.To_Set (F),
                        Var_Ex_Use =>
                          Process_Discriminants
                            (Intermediate_Vars_Used => Constraint_Vars,
                             Var_Defined            => F),
                        Subp_Calls => Funcalls,
                        Indt_Calls => Indcalls,
                        Vertex_Ctx => Ctx.Vertex_Ctx,
                        E_Loc      => N,
                        Print_Hint => Pretty_Print_Record_Field),
                     V);
                  Inits.Append (V);
               end;
            elsif Is_Default_Initialized (F) then
               Add_Vertex
                 (FA,
                  Make_Default_Initialization_Attributes
                    (FA         => FA,
                     Scope      => FA.B_Scope,
                     F          => F,
                     Vertex_Ctx => Ctx.Vertex_Ctx),
                  V);
               Inits.Append (V);
            end if;
         end loop;

         --  If this type has a Default_Initial_Condition (DIC) then we need to
         --  create a vertex to check for uninitialized variables within
         --  the Default_Initial_Condition's expression. For imported objects
         --  the DIC expression is not evaluated.
         --  ??? what about DIC evaluated for individual components?

         if not Is_Imported (E) and then Has_DIC (Typ) then
            declare
               procedure Add_Vertex_For_All_DIC is new
                 Iterate_Applicable_DIC (Add_Vertex_For_DIC);
            begin
               Add_Vertex_For_All_DIC (Typ);
            end;
         end if;

      end if;

      --  If nothing has been initialized by this object declaration, then add
      --  a dummy vertex.

      if Inits.Is_Empty then
         Add_Dummy_Vertex (N, FA, CM);

      --  Otherwise, link all initialization vertices

      else
         V := Flow_Graphs.Null_Vertex;
         for W of Inits loop
            if V /= Flow_Graphs.Null_Vertex then
               Linkup (FA, V, W);
            end if;
            V := W;
         end loop;
         CM.Insert
           (Union_Id (N),
            Graph_Connections'
              (Standard_Entry => Inits.First_Element,
               Standard_Exits => To_Set (Inits.Last_Element)));
      end if;

      --  If we are analyzing a package spec or body and we just introduced
      --  'Initial and 'Final vertices for an entity that is mentioned in an
      --  Initializes aspect, we have to set Is_Export on the corresponding
      --  'Final vertices.
      if FA.Kind = Kind_Package and then Present (Find_In_Initializes (E)) then
         for F of Flatten_Variable (E, FA.B_Scope) loop
            declare
               Final_F_Id : constant Flow_Id :=
                 Change_Variant (F, Final_Value);

               Final_V_Id : constant Flow_Graphs.Vertex_Id :=
                 FA.CFG.Get_Vertex (Final_F_Id);

               Final_Atr : V_Attributes renames FA.Atr (Final_V_Id);

            begin
               Final_Atr.Is_Export :=
                 Final_Atr.Is_Export
                 or else Is_Initialized_At_Elaboration (E, FA.B_Scope);
            end;
         end loop;
      end if;

      --  In phase 1 we register task instances and priorities of objects
      --  containing protected types. Both can be only declared as library
      --  level entities (because of the Ravenscar profile restrictions).
      --  We only register those declared directly within the scope of the
      --  analyzed package (i.e. not those in nested packages), because we
      --  want to register them only once.
      if FA.Generating_Globals
        and then Ekind (FA.Spec_Entity) = E_Package
        and then Scope (E) = FA.Spec_Entity
        and then Is_Library_Level_Entity (E)
      then
         declare
            T : constant Entity_Id := Etype (E);

         begin
            --  Register task objects
            Find_Tasks (T, Size => 0);
         end;
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
      Spec_E : constant Entity_Id := Defining_Entity (N);

   begin
      --  If the nested package is not in SPARK (either because of explicit
      --  SPARK_Mode => Off or because a SPARK violation), then ignore its
      --  abstract states, visible declarations and private declarations. The
      --  Initializes contract, if present, will be ignored when processing the
      --  package body, if present.

      if not Entity_In_SPARK (Spec_E) then
         Add_Dummy_Vertex (N, FA, CM);
         return;
      end if;

      --  Introduce variables from the Abstract_State aspect of the nested
      --  package.

      if Has_Non_Null_Abstract_State (Spec_E) then
         for State of Iter (Abstract_States (Spec_E)) loop
            --  Creating 'Initial and 'Final vertices for every state
            --  abstraction and setting Is_Export to True if the
            --  corresponding entity is initialized.
            declare
               Final_F_Id : constant Flow_Id :=
                 Change_Variant (Direct_Mapping_Id (State), Final_Value);

               Final_V_Id : Flow_Graphs.Vertex_Id :=
                 FA.CFG.Get_Vertex (Final_F_Id);

            begin
               Create_Initial_And_Final_Vertices (State, FA);

               if FA.Kind = Kind_Package then
                  Final_V_Id := FA.CFG.Get_Vertex (Final_F_Id);

                  declare
                     Final_Atr : V_Attributes renames FA.Atr (Final_V_Id);

                  begin
                     Final_Atr.Is_Export :=
                       Final_Atr.Is_Export
                       or else Is_Initialized_At_Elaboration
                                 (State, FA.B_Scope);
                  end;
               end if;
            end;

            Register_Own_Variable (FA, State);
         end loop;
      end if;

      --  Traverse visible and private part of the specs and link them up

      declare
         Spec : constant Node_Id := Specification (N);

         Visible_Decls : constant List_Id := Visible_Declarations (Spec);
         Private_Decls : constant List_Id := Private_Declarations (Spec);

         V : Flow_Graphs.Vertex_Id;
         --  Vertex that represents elaboration of a nested package

         Save_In_Nested_Package : constant Boolean :=
           Ctx.Vertex_Ctx.In_Nested_Package;

      begin
         --  Pretend that declaration of an immediately nested package is a
         --  "call", so that calls from the elaboration of that package will
         --  appear as calls from the analyzed entity.
         --
         --  Don't do this for wrapper packages, because they are not
         --  flow-analyzed and we do not get direct calls for them; in effect,
         --  we wouldn't be able to resolve calls from their elaboration (but
         --  there shouldn't be any such calls anyway).

         Add_Vertex
           (FA,
            Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Subp_Calls =>
                 (if Enclosing_Unit (Spec_E) = FA.Spec_Entity
                    and then not Is_Wrapper_Package (Spec_E)
                  then Call_Sets.To_Set (Subprogram_Call'(N => N, E => Spec_E))
                  else Call_Sets.Empty_Set),
               Vertex_Ctx =>
                 (No_Vertex_Context
                  with delta
                    In_Nested_Package => Ctx.Vertex_Ctx.In_Nested_Package),
               E_Loc      => N,
               Print_Hint => Pretty_Print_Package),
            V);

         Ctx.Vertex_Ctx.In_Nested_Package := True;

         Process_Statement_List (Visible_Decls, FA, CM, Ctx);

         --  Link the trivial vertex for package elaboration with vertices
         --  for its visible declarations.
         Linkup (FA, V, CM (Union_Id (Visible_Decls)).Standard_Entry);

         --  Process the private declarations if they are present and in SPARK
         if No (Get_Pragma (Spec_E, Pragma_Abstract_State))
           and then Present (Private_Decls)
           and then Private_Spec_In_SPARK (Spec_E)
         then
            Process_Statement_List (Private_Decls, FA, CM, Ctx);

            --  Link the visible declarations to the private declarations
            Linkup
              (FA,
               CM (Union_Id (Visible_Decls)).Standard_Exits,
               CM (Union_Id (Private_Decls)).Standard_Entry);

            --  The standard entry of N is the entry to the visible
            --  declarations and the standard exits are the exits of the
            --  private declarations.
            CM.Insert
              (Union_Id (N),
               Graph_Connections'
                 (Standard_Entry => V,
                  Standard_Exits =>
                    CM.Element (Union_Id (Private_Decls)).Standard_Exits));

            CM.Delete (Union_Id (Visible_Decls));
            CM.Delete (Union_Id (Private_Decls));

         --  We have only processed the visible declarations so we just copy
         --  the connections of N from Visible_Decls.

         else
            CM.Insert
              (Union_Id (N),
               Graph_Connections'
                 (Standard_Entry => V,
                  Standard_Exits =>
                    CM.Element (Union_Id (Visible_Decls)).Standard_Exits));

            CM.Delete (Union_Id (Visible_Decls));
         end if;

         Ctx.Vertex_Ctx.In_Nested_Package := Save_In_Nested_Package;

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
      Package_Spec : constant Entity_Id := Unique_Defining_Entity (N);

      Elaboration_Has_Effect : constant Boolean :=
        No (Get_Pragma (Package_Spec, Pragma_Abstract_State))
        and then Entity_Body_In_SPARK (Package_Spec);

      Pkg_Body : constant Node_Id := Package_Body (Package_Spec);
      --  Proper body, irrespecitve whether N is a stub or not

      pragma Assert (Nkind (Pkg_Body) = N_Package_Body);

      Pkg_Body_Declarations : constant List_Id := Declarations (Pkg_Body);

      DM : constant Dependency_Maps.Map :=
        Parse_Initializes (Package_Spec, FA.B_Scope);

      Save_In_Nested_Package : constant Boolean :=
        Ctx.Vertex_Ctx.In_Nested_Package;

   begin
      --  If package spec is not in SPARK, then ignore its body and its
      --  Initializes contract, if any.

      if not Entity_In_SPARK (Package_Spec) then
         Add_Dummy_Vertex (N, FA, CM);

      --  If neither elaboration or Initializes has any effect then create only
      --  a null vertex.

      elsif DM.Is_Empty and then not Elaboration_Has_Effect then
         Add_Dummy_Vertex (N, FA, CM);

      else
         Ctx.Vertex_Ctx.In_Nested_Package := True;

         if Elaboration_Has_Effect then
            --  Traverse package body declarations
            Process_Statement_List (Pkg_Body_Declarations, FA, CM, Ctx);
         end if;

         --  The package has been now elaborated and vertices for the variables
         --  in the package body declarations are created. Now apply the
         --  Initializes aspect, if present.

         if DM.Is_Empty then
            Move_Connections
              (CM,
               Dst => Union_Id (N),
               Src => Union_Id (Pkg_Body_Declarations));
         else
            declare
               Init_Items     : Union_Lists.List := Union_Lists.Empty_List;
               Initializes_CM : Graph_Connections;
            begin
               for C in DM.Iterate loop
                  declare
                     The_Out : Flow_Id renames Dependency_Maps.Key (C);
                     The_Ins : Flow_Id_Sets.Set renames DM (C);

                     Init_Item : constant Entity_Id :=
                       (if Present (The_Out)
                        then Get_Direct_Mapping_Id (The_Out)
                        else Types.Empty);
                     --  If Init_Item = Types.Empty, we are in the case of a
                     --  "null => ..." Initializes contract. We will create
                     --  a vertex to read the RHS of the contract and insert
                     --  it in the Connections Map.

                     V : Flow_Graphs.Vertex_Id;

                  begin
                     Init_Items.Append (Union_Id (Init_Item));

                     Add_Vertex
                       (FA,
                        Make_Package_Initialization_Attributes
                          (The_State  => The_Out,
                           Inputs     => The_Ins,
                           Scope      => FA.B_Scope,
                           Vertex_Ctx => Ctx.Vertex_Ctx,
                           E_Loc      =>
                             (if Present (Init_Item) then Init_Item else N)),
                        V);
                     CM.Insert (Union_Id (Init_Item), Trivial_Connection (V));

                  end;
               end loop;

               Join
                 (FA    => FA,
                  CM    => CM,
                  Nodes => Init_Items,
                  Block => Initializes_CM);

               if Elaboration_Has_Effect then
                  --  We connect the Declarations of the body to the
                  --  Initializes_CM.
                  Linkup
                    (FA,
                     CM (Union_Id (Pkg_Body_Declarations)).Standard_Exits,
                     Initializes_CM.Standard_Entry);

                  --  We set the standard entry of N to the standard entry
                  --  of the body's declarations and the standard exists of N
                  --  to the standard exists of the last element in the Verts
                  --  union list.
                  CM.Insert
                    (Union_Id (N),
                     Graph_Connections'
                       (Standard_Entry =>
                          CM.Element (Union_Id (Pkg_Body_Declarations))
                            .Standard_Entry,
                        Standard_Exits => Initializes_CM.Standard_Exits));

                  CM.Delete (Union_Id (Pkg_Body_Declarations));
               else
                  --  Since we do not process any declarations all we have to
                  --  do is to connect N to the Initializes_CM.
                  CM.Insert (Union_Id (N), Initializes_CM);
               end if;
            end;
         end if;

         Ctx.Vertex_Ctx.In_Nested_Package := Save_In_Nested_Package;
      end if;
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
      --  breaking on fip will get you to that point in the program.

      function Add_Loop_Entry_Reference (N : Node_Id) return Traverse_Result;
      --  Adds N to the appropriate entry references of the current
      --  context, if N is a loop_entry reference.

      -------------------------
      -- Find_Execution_Kind --
      -------------------------

      function Find_Execution_Kind return Execution_Kind_T is
      begin
         if Get_Pragma_Id (N) = Pragma_Check then
            declare
               Arg1 : constant Node_Id :=
                 First (Pragma_Argument_Associations (N));

               Was_Assertion : constant Boolean :=
                 (Present (Arg1)
                  and then Nkind (Expression (Arg1)) = N_Identifier
                  and then Chars (Expression (Arg1)) = Name_Assert);
               --  True if this pragma is a rewritten assert pragma

               function Is_Statically_False return Boolean;
               --  Checks if the rewritten assertion has a statically-false
               --  argument.

               -------------------------
               -- Is_Statically_False --
               -------------------------

               function Is_Statically_False return Boolean is
                  Arg2 : constant Node_Id := Next (Arg1);
               begin
                  return
                    Present (Arg2)
                    and then Nkind (Expression (Arg2))
                             in N_Expanded_Name | N_Identifier
                    and then Entity (Expression (Arg2)) = Standard_False;
               end Is_Statically_False;

            begin
               return
                 (if Was_Assertion and then Is_Statically_False
                  then Abnormal_Termination
                  else Normal_Execution);
            end;

         else
            return Normal_Execution;
         end if;
      end Find_Execution_Kind;

      ---------
      -- fip --
      ---------

      procedure fip is
      begin
         null;
      end fip;

      ------------------------------
      -- Add_Loop_Entry_Reference --
      ------------------------------

      function Add_Loop_Entry_Reference (N : Node_Id) return Traverse_Result is
         Loop_Name : Node_Id;
      begin
         if Is_Attribute_Loop_Entry (N) then
            pragma Assert (Present (Ctx.Active_Loop));

            --  This is a named loop entry reference, e.g. "X'Loop_Entry (Foo)"

            if Present (Expressions (N)) then

               pragma Assert (List_Length (Expressions (N)) = 1);
               Loop_Name := First (Expressions (N));

               pragma Assert (Nkind (Loop_Name) = N_Identifier);
               Ctx.Entry_References (Entity (Loop_Name)).Include (N);

            --  or otherwise a reference to the immediately enclosing loop

            else
               Ctx.Entry_References (Ctx.Active_Loop).Include (N);
            end if;
         end if;

         return OK;
      end Add_Loop_Entry_Reference;

      procedure Add_Loop_Entry_References is new
        Traverse_More_Proc (Add_Loop_Entry_Reference);

      V        : Flow_Graphs.Vertex_Id;
      Funcalls : Call_Sets.Set;
      Indcalls : Node_Sets.Set;

      --  Start of processing for Do_Pragma

   begin
      if Pragma_Relevant_To_Flow (N) then

         --  If we are processing a pragma that is relevant to flow analysis,
         --  and we are not dealing with either pragma unmodified or
         --  pragma unreferenced then we create a sink vertex to check
         --  for uninitialized variables.
         Pick_Generated_Info
           (N,
            FA.B_Scope,
            Function_Calls     => Funcalls,
            Indirect_Calls     => Indcalls,
            Proof_Dependencies => FA.Proof_Dependencies,
            Tasking            => FA.Tasking,
            Generating_Globals => FA.Generating_Globals);

         --  Syntax for pragmas relevant to flow is:
         --
         --    pragma Check (
         --       [Name    =>] CHECK_KIND,
         --       [Check   =>] Boolean_EXPRESSION
         --    [, [Message =>] string_EXPRESSION] );
         --
         --    pragma Loop_Invariant ( boolean_EXPRESSION );
         --
         --  and we are only interested in boolean_EXPRESSION.

         Add_Vertex
           (FA,
            Direct_Mapping_Id (N),
            Make_Sink_Vertex_Attributes
              (Var_Use      =>
                 Get_All_Variables
                   (Expression
                      (case Get_Pragma_Id (N) is
                         when Pragma_Check =>
                           Next (First (Pragma_Argument_Associations (N))),
                         when Pragma_Loop_Variant =>
                           First (Pragma_Argument_Associations (N)),
                         when others => raise Program_Error),
                    Scope                => FA.B_Scope,
                    Target_Name          => Null_Flow_Id,
                    Use_Computed_Globals => not FA.Generating_Globals),
               Subp_Calls   => Funcalls,
               Indt_Calls   => Indcalls,
               Is_Assertion => True,
               Vertex_Ctx   => Ctx.Vertex_Ctx,
               E_Loc        => N,
               Execution    => Find_Execution_Kind),
            V);

      else
         --  Otherwise we produce a null vertex
         Add_Vertex (FA, Null_Node_Attributes, V);

         --  Pragma Inspection_Point is also ignored, but we insert a call
         --  to a dummy procedure, to allow to break on it during
         --  debugging.

         if Get_Pragma_Id (N) = Pragma_Inspection_Point then
            fip;
         end if;

      end if;

      CM.Insert (Union_Id (N), Trivial_Connection (V));

      --  We make a note of 'Loop_Entry uses
      if Get_Pragma_Id (N)
         in Pragma_Check | Pragma_Loop_Variant | Pragma_Loop_Invariant
      then
         Add_Loop_Entry_References (N);
      end if;

      --  If we find a pragma Loop_Variant we set the Termination_Proved flag

      if Get_Pragma_Id (N) = Pragma_Loop_Variant then
         Ctx.Termination_Proved := True;
      end if;

   end Do_Pragma;

   ------------------------
   -- Do_Raise_Statement --
   ------------------------

   procedure Do_Raise_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V, V_Raise : Flow_Graphs.Vertex_Id;
      Unused     : Boolean;

      Par : Node_Id;
      --  Iterator for finding the parent of the corresponding handler

      Mark : Borrowers_Markers.Cursor;
      --  Once we know which sequence_of_statements we will jump to, it will
      --  point to the number of local borrowers at that point.

      Top : Node_Lists.Cursor;
      --  Iterator for the borrowers reclaimed when jumping with goto

      Expr           : constant Node_Id := Expression (N);
      Local_Handlers : constant Node_Lists.List := Reachable_Handlers (N);

      Funcalls : Call_Sets.Set;
      Indcalls : Node_Sets.Set;
      Vars     : Flow_Id_Sets.Set;

   begin
      --  Pick reads and calls from the string_expression, if any

      if Present (Expr) then
         Pick_Generated_Info
           (Expr,
            FA.B_Scope,
            Function_Calls     => Funcalls,
            Indirect_Calls     => Indcalls,
            Proof_Dependencies => FA.Proof_Dependencies,
            Tasking            => FA.Tasking,
            Generating_Globals => FA.Generating_Globals);

         Vars :=
           Get_Variables
             (Expr,
              Scope                => FA.B_Scope,
              Target_Name          => Null_Flow_Id,
              Fold_Functions       => Inputs,
              Use_Computed_Globals => not FA.Generating_Globals);

         Ctx.Folded_Function_Checks.Append (Expr);
      end if;

      Add_Vertex
        (FA,
         Direct_Mapping_Id (N),
         Make_Sink_Vertex_Attributes
           (Var_Use    => Vars,
            Subp_Calls => Funcalls,
            Indt_Calls => Indcalls,
            Vertex_Ctx => Ctx.Vertex_Ctx,
            E_Loc      => N),
         V_Raise);

      --  If there are no local handlers, it is an abnormal execution

      if Local_Handlers.Is_Empty then

         --  Flag the raise statement as abnormal termination, while not being
         --  a program node (to suppress various warnings).

         FA.Atr (V_Raise).Execution := Abnormal_Termination;
         FA.Atr (V_Raise).Is_Program_Node := False;

      --  Otherwise, RAISE behaves like a GOTO statement

      else
         null;
      end if;

      CM.Insert
        (Union_Id (N),
         Graph_Connections'
           (Standard_Entry => V_Raise,
            Standard_Exits => Vertex_Sets.Empty_Set));

      for Handler of Local_Handlers loop
         V := V_Raise;

         --  For exception that has a local handler we reclaim the borrowed
         --  objects and record a jump to the exception handler.

         if Nkind (Handler) = N_Exception_Handler then
            --  Go up the tree until we find the parent of the
            --  sequence_of_statements we are jumping to and move the cursor
            --  at each block that we jump out from.

            Mark := Ctx.Borrow_Numbers.Last;
            Par := N;

            loop
               Par := Parent (Par);
               exit when
                 Nkind (Par) = N_Handled_Sequence_Of_Statements
                 and then List_Containing (Handler) = Exception_Handlers (Par);
               if Nkind (Par) = N_Block_Statement then
                  Borrowers_Markers.Previous (Mark);
               end if;
            end loop;

            --  When borrowers go out of scope, we pop them from the stack and
            --  assign back to the borrowed objects. This way we keep track of
            --  anything that happened while they were borrowed.

            Top := Ctx.Borrowers.Last;

            for J in Ctx.Borrow_Numbers (Mark) + 1 .. Ctx.Borrowers.Length loop
               Reclaim_Borrower (Ctx.Borrowers (Top), FA, Last => V);
               Node_Lists.Previous (Top);
            end loop;

            Linkup
              (FA, From => V, To => CM (Union_Id (Handler)).Standard_Entry);

         --  Deal with exception that is only listed in Exceptional_Cases

         else
            for Decl of reverse Ctx.Borrowers loop
               Reclaim_Borrower (Decl, FA, Last => V);
            end loop;

            --  Link the last vertex directly to the exceptional end vertex,
            --  i.e. bypass evaluation of any postconditions.
            Linkup (FA, From => V, To => FA.Exceptional_End_Vertex);
         end if;
      end loop;
   end Do_Raise_Statement;

   ------------------------
   -- Do_Raise_xxx_Error --
   ------------------------

   procedure Do_Raise_xxx_Error
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
           (E_Loc => N, Execution => Abnormal_Termination),
         V);
      CM.Insert
        (Union_Id (N),
         Graph_Connections'
           (Standard_Entry => V, Standard_Exits => Vertex_Sets.Empty_Set));
   end Do_Raise_xxx_Error;

   -----------------------
   -- Do_Call_Statement --
   -----------------------

   procedure Do_Call_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      Called_Thing : constant Entity_Id := Get_Called_Entity (N);

      procedure Check_Visibility
      with Ghost;
      --  Sanity-check that callee is visible to the caller. This exercises the
      --  visibility machinery which otherwise is primarily used for constructs
      --  that are far less common, e.g. private types and Part_Ofs.

      procedure Handle_Exception
        (Branch : Flow_Graphs.Vertex_Id; Handler : Node_Id);
      --  Transfer control from Branch to Handler when the called subprogram
      --  raises an exception. In particular, reclaim local borrowers.

      ----------------------
      -- Check_Visibility --
      ----------------------

      procedure Check_Visibility is
         Called_Loc : constant Flow_Scope := Get_Flow_Scope (Called_Thing);
         pragma Assert (Called_Loc.Ent = Called_Thing);
         --  Sanity check: the called subprogram is located in its own scope

         --  We only check the Ent component of Called_Loc because the Part
         --  component is either Visible_Part (for subprograms with explicit
         --  spec) or Body_Part (for subprograms whose bodies act as specs).

         Called_Scop : constant Flow_Scope := (Called_Loc.Ent, Visible_Part);

         --  Sanity check: the caller can see the called subprogram, or, the
         --  called subprogram is a dispatching operation declared in a private
         --  part (SPARK RM 3.9.2 (20.1/3)).

         pragma
           Assert
             ((Is_Dispatching_Operation (Called_Thing)
               and then Is_Hidden (Called_Thing))
                or else Is_Visible (Called_Scop, FA.B_Scope));
      begin
         null;
      end Check_Visibility;

      ----------------------
      -- Handle_Exception --
      ----------------------

      procedure Handle_Exception
        (Branch : Flow_Graphs.Vertex_Id; Handler : Node_Id)
      is
         Reclaim : Flow_Graphs.Vertex_Id := Branch;
         --  Pointer to the vertex for reclaiming a borrower when jumping to an
         --  exception handler.

         Mark : Borrowers_Markers.Cursor;
         --  Once we know which sequence_of_statements we will jump to, it will
         --  point to the number of local borrowers at that point.

         Top : Node_Lists.Cursor;
         --  Iterator for the borrowers reclaimed when jumping with raise

         Par : Node_Id;
         --  Iterator for finding the parent of the corresponding handler

      begin
         --  For exception that has a local handler we reclaim the borrowed
         --  objects and record a jump to the exception handler.

         if Nkind (Handler) = N_Exception_Handler then
            --  Go up the tree until we find the parent of the
            --  sequence_of_statements we are jumping to and move the cursor
            --  at each block that we jump out from.

            Mark := Ctx.Borrow_Numbers.Last;
            Par := N;

            loop
               Par := Parent (Par);
               exit when
                 Nkind (Par) = N_Handled_Sequence_Of_Statements
                 and then List_Containing (Handler) = Exception_Handlers (Par);
               if Nkind (Par) = N_Block_Statement then
                  Borrowers_Markers.Previous (Mark);
               end if;
            end loop;

            --  When borrowers go out of scope, we pop them from the stack and
            --  assign back to the borrowed objects. This way we keep track of
            --  anything that happened while they were borrowed.

            Top := Ctx.Borrowers.Last;

            for J in Ctx.Borrow_Numbers (Mark) + 1 .. Ctx.Borrowers.Length loop
               Reclaim_Borrower (Ctx.Borrowers (Top), FA, Last => Reclaim);
               Node_Lists.Previous (Top);
            end loop;

            Linkup
              (FA,
               From => Reclaim,
               To   => CM (Union_Id (Handler)).Standard_Entry);

         --  For exception that is only listed in Exceptional_Cases we reclaim
         --  the borrowers and jump out of the subprogram.

         else
            for Decl of reverse Ctx.Borrowers loop
               Reclaim_Borrower (Decl, FA, Last => Reclaim);
            end loop;

            --  Link the last vertex directly to the exceptional end vertex,
            --  i.e. bypass evaluation of any postconditions.
            Linkup (FA, From => Reclaim, To => FA.Exceptional_End_Vertex);
         end if;
      end Handle_Exception;

      Ins                 : Vertex_Lists.List;
      Outs_By_Copy        : Vertex_Lists.List;
      Outs_By_Reference   : Vertex_Lists.List;
      Outs_By_Unspecified : Vertex_Lists.List;

      V : Flow_Graphs.Vertex_Id;
      C : Flow_Graphs.Cluster_Id;

      Excp  : Flow_Graphs.Vertex_Id;
      Havoc : Flow_Graphs.Vertex_Id;
      --  Vertices for branching the control flow when the called subprogram
      --  raises an exception and for havocing its parameters passed,
      --  respectively.

      Program_Exit : Flow_Graphs.Vertex_Id;
      --  Vertex to capture what happens when the callee might exit the program

      Local_Handlers : constant Node_Lists.List :=
        (if Nkind (N) in N_Subprogram_Call
         then Reachable_Handlers (N)
         else Node_Lists.Empty_List);

      Vars_Used : Flow_Id_Sets.Set;
      Funcalls  : Call_Sets.Set;
      Indcalls  : Node_Sets.Set;

   begin
      --  Visibility checks don't make much sense for access-to-subprograms

      if Ekind (Called_Thing) /= E_Subprogram_Type then
         Check_Visibility;
      end if;

      if FA.Generating_Globals and then Flow_Classwide.Is_Dispatching_Call (N)
      then
         Process_Dispatching_Call (N, FA.Proof_Dependencies);
      end if;

      --  Add a cluster to help pretty printing
      FA.CFG.New_Cluster (C);

      --  For calls via access-to-subprogram handle variables referenced in the
      --  prefix.

      if Ekind (Called_Thing) = E_Subprogram_Type then
         declare
            Pref : constant Node_Id := Prefix (Name (N));
         begin
            Vars_Used :=
              Get_Variables
                (Pref,
                 Scope                => FA.B_Scope,
                 Target_Name          => Null_Flow_Id,
                 Fold_Functions       => Inputs,
                 Use_Computed_Globals => not FA.Generating_Globals);

            Pick_Generated_Info
              (Pref,
               FA.B_Scope,
               Function_Calls     => Funcalls,
               Indirect_Calls     => Indcalls,
               Proof_Dependencies => FA.Proof_Dependencies,
               Tasking            => FA.Tasking,
               Generating_Globals => FA.Generating_Globals);

            Ctx.Folded_Function_Checks.Append (Pref);
         end;
      end if;

      --  A vertex for the actual call
      Add_Vertex
        (FA,
         Direct_Mapping_Id (N),
         Make_Call_Attributes
           (Callsite   => N,
            Var_Use    => Vars_Used,
            Subp_Calls =>
              Call_Sets.To_Set (Subprogram_Call'(N => N, E => Called_Thing))
                .Union (Funcalls),
            Indt_Calls => Indcalls,
            Vertex_Ctx => Ctx.Vertex_Ctx,
            E_Loc      => N),
         V);
      FA.CFG.Set_Cluster (V, C);

      --  Deal with the subprogram's parameters
      Process_Call_Actuals
        (N,
         Ins,
         Outs_By_Copy,
         Outs_By_Reference,
         Outs_By_Unspecified,
         FA,
         CM,
         Ctx);

      --  We process globals when:
      --     * the globals have already been generated or
      --     * when the user has supplied them and we don't have to rely
      --       on the generated ones
      --  ??? for this decision we rely on condition hardcoded in Get_Globals,
      --  just like we do in Do_Subprogram_Call when processing function calls
      if Ekind (Called_Thing) /= E_Subprogram_Type then
         Process_Subprogram_Globals (N, Ins, Outs_By_Reference, FA, CM, Ctx);
      end if;

      --  A magic null export is needed when:
      --    * there is a usable Depends => (null => ...);
      --    * the subprogram has imports but no exports
      --
      --  Notice that we can only use the Depends when it:
      --    * does not need to be refined or
      --    * it has already been refined
      if Ekind (Called_Thing) /= E_Subprogram_Type
        and then Has_Depends (Called_Thing)
        and then (not FA.Generating_Globals
                  or else not Rely_On_Generated_Global
                                (Called_Thing, FA.B_Scope))
      then
         --  Check if there exists a usable Depends => (null => ...)
         declare
            D_Map : Dependency_Maps.Map;
            V     : Flow_Graphs.Vertex_Id;

            Null_Depends : Dependency_Maps.Cursor;

         begin
            Get_Depends
              (Subprogram           => Called_Thing,
               Scope                => FA.B_Scope,
               Classwide            => Flow_Classwide.Is_Dispatching_Call (N),
               Depends              => D_Map,
               Use_Computed_Globals => not FA.Generating_Globals);

            Null_Depends := D_Map.Find (Null_Flow_Id);

            if Dependency_Maps.Has_Element (Null_Depends) then

               pragma Assert (not D_Map (Null_Depends).Is_Empty);

               Add_Vertex
                 (FA,
                  Make_Global_Attributes
                    (Callsite   => N,
                     Global     =>
                       Change_Variant (Null_Export_Flow_Id, Out_View),
                     Mode       => Mode_Out,
                     Scope      => FA.B_Scope,
                     Vertex_Ctx => Ctx.Vertex_Ctx,
                     E_Loc      => N),
                  V);
               Outs_By_Reference.Append (V);
            end if;
         end;
      elsif not Ins.Is_Empty
        and then Outs_By_Copy.Is_Empty
        and then Outs_By_Reference.Is_Empty
        and then Outs_By_Unspecified.Is_Empty
      then
         declare
            V : Flow_Graphs.Vertex_Id;
         begin
            Add_Vertex
              (FA,
               Make_Global_Attributes
                 (Callsite   => N,
                  Global     => Change_Variant (Null_Export_Flow_Id, Out_View),
                  Mode       => Mode_Out,
                  Scope      => FA.B_Scope,
                  Vertex_Ctx => Ctx.Vertex_Ctx,
                  E_Loc      => N),
               V);
            Outs_By_Reference.Append (V);
         end;
      end if;

      --  We now build the connection map for this sequence
      declare
         Prev : Flow_Graphs.Vertex_Id := V;
         --  Pointer to the previous vertex, initialized to V which goes first

      begin
         for Var of Ins loop
            FA.CFG.Set_Cluster (Var, C);
            FA.CFG.Add_Edge (Prev, Var, EC_Default);
            Prev := Var;
         end loop;

         for Var of Outs_By_Reference loop
            FA.CFG.Set_Cluster (Var, C);
            FA.CFG.Add_Edge (Prev, Var, EC_Default);
            Prev := Var;
         end loop;

         --  We only create vertices related to exception handlers when they
         --  are actually needed, because with a degenerated graph like this:
         --
         --    call P
         --    |
         --    <raise>   ---   <havoc>
         --    |
         --
         --  the <havoc> vertex with no out-edges would be recognized as
         --  raising an exception, prunned and consequently the <raise>
         --  vertex would be recognized as a branch preventing exception from
         --  being raised. In turn, this would render all call statements as
         --  effective, even those which have no effect at all.

         if not Local_Handlers.Is_Empty then
            Add_Vertex
              (FA,
               Make_Basic_Attributes
                 (Vertex_Ctx => Ctx.Vertex_Ctx,
                  E_Loc      => N,
                  Print_Hint => Pretty_Print_Call_Exception),
               Excp);
            FA.Atr (Excp).Is_Call_Exception := True;
            FA.Atr (Excp).Is_Program_Node := False;
            FA.CFG.Set_Cluster (Excp, C);
            FA.CFG.Add_Edge (Prev, Excp, EC_Default);

            Prev := Excp;
         end if;

         for Var of Outs_By_Copy loop
            FA.CFG.Set_Cluster (Var, C);
            FA.CFG.Add_Edge (Prev, Var, EC_Default);
            Prev := Var;
         end loop;

         for Var of Outs_By_Unspecified loop
            FA.CFG.Set_Cluster (Var, C);
            FA.CFG.Add_Edge (Prev, Var, EC_Default);
            Prev := Var;
         end loop;

         --  When the callee might exit the program, we simply assert its
         --  Program_Exit expression.

         --  ??? Might_Exit_Program contains 2 parts: one that looks at the
         --  callee, and one another that looks at the context. The second
         --  part could be separated, so we would use Ctx.

         if Might_Exit_Program (N) then
            Add_Vertex
              (FA,
               Make_Sink_Vertex_Attributes
                 (Var_Use      =>
                    Get_Outputs_From_Program_Exit
                      (FA.Spec_Entity, FA.B_Scope, not FA.Generating_Globals),
                  Vertex_Ctx   => Ctx.Vertex_Ctx,
                  E_Loc        => N,
                  Is_Assertion => True),
               Program_Exit);

            FA.Atr (Program_Exit).Pretty_Print_Kind :=
              Pretty_Print_Program_Exit;

            FA.CFG.Set_Cluster (Program_Exit, C);
            FA.CFG.Add_Edge (Prev, Program_Exit, EC_Default);
            Prev := Program_Exit;
         end if;

         --  Abnormal execution is when the callee has No_Return, but the
         --  caller is an ordinary unit (i.e. without No_Return).

         if Is_Subprogram (Called_Thing)
           and then No_Return (Called_Thing)
           and then not Is_Possibly_Nonreturning_Procedure (FA.Spec_Entity)
         then
            CM.Insert
              (Union_Id (N),
               Graph_Connections'
                 (Standard_Entry => V,
                  Standard_Exits => Vertex_Sets.Empty_Set));
            FA.Atr (V).Execution :=
              Get_Execution_Kind
                (Called_Thing, After_GG => not FA.Generating_Globals);
            Linkup (FA, Prev, FA.Helper_End_Vertex);
         else
            CM.Insert
              (Union_Id (N),
               Graph_Connections'
                 (Standard_Entry => V,
                  Standard_Exits => Vertex_Sets.To_Set (Prev)));

            if not Local_Handlers.Is_Empty then
               --  Create the <havoc> vertex and populate it with variables
               --  that are actually havoced.

               Add_Vertex
                 (FA,
                  Make_Basic_Attributes
                    (Vertex_Ctx => Ctx.Vertex_Ctx,
                     E_Loc      => N,
                     Print_Hint => Pretty_Print_Param_Havoc),
                  Havoc);
               FA.Atr (Havoc).Is_Param_Havoc := True;
               FA.Atr (Havoc).Is_Program_Node := False;
               FA.CFG.Set_Cluster (Havoc, C);
               FA.CFG.Add_Edge (Excp, Havoc, EC_Default);

               for Out_By_Unspecified of Outs_By_Unspecified loop
                  pragma Assert (FA.Atr (Out_By_Unspecified).Is_Parameter);
                  pragma
                    Assert
                      (FA.CFG.Get_Key (Out_By_Unspecified).Variant = Out_View);

                  FA.Atr (Havoc).Variables_Defined.Union
                    (FA.Atr (Out_By_Unspecified).Variables_Defined);
               end loop;

               --  Connect havoc with exception handlers

               for Handler of Local_Handlers loop
                  Handle_Exception (Havoc, Handler);
               end loop;
            end if;
         end if;
      end;

      if FA.Generating_Globals then
         --  Check for calls to protected procedures and entries
         --
         --  Ignore calls from within the same protected type (internal)
         --  including calls from protected procedure to entry of the same
         --  protected type. These calls are already reported as potentially
         --  blocking.
         --  Only register tasking-related info for calls from the outside of
         --  the protected type (external).

         if Ekind (Scope (Called_Thing)) = E_Protected_Type
           and then Is_External_Call (N)
         then
            if Is_Entry (Called_Thing) then
               FA.Entries.Include
                 (Entry_Call'
                    (Prefix => Prefix (Name (N)), Entr => Called_Thing));
            end if;

            FA.Tasking (Locks).Include
              (Get_Enclosing_Object (Prefix (Name (N))));
         end if;

         --  Check for suspending on a suspension object
         if Suspends_On_Suspension_Object (Called_Thing) then
            FA.Tasking (Suspends_On).Include
              (Get_Enclosing_Object (First_Actual (N)));
         end if;
      end if;
   end Do_Call_Statement;

   ----------------------------
   -- Do_Contract_Expression --
   ----------------------------

   procedure Do_Contract_Expression
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      pragma Unmodified (Ctx);

      V        : Flow_Graphs.Vertex_Id;
      Funcalls : Call_Sets.Set;
      Indcalls : Node_Sets.Set;
   begin
      --  We just need to check for uninitialized variables
      Pick_Generated_Info
        (N,
         FA.B_Scope,
         Function_Calls     => Funcalls,
         Indirect_Calls     => Indcalls,
         Proof_Dependencies => FA.Proof_Dependencies,
         Tasking            => FA.Tasking,
         Generating_Globals => FA.Generating_Globals);

      Add_Vertex
        (FA,
         Direct_Mapping_Id (N),
         Make_Sink_Vertex_Attributes
           (Var_Use      =>
              Get_All_Variables
                (N,
                 Scope                => FA.B_Scope,
                 Target_Name          => Null_Flow_Id,
                 Use_Computed_Globals => not FA.Generating_Globals),
            Subp_Calls   => Funcalls,
            Indt_Calls   => Indcalls,
            Is_Assertion => True,
            Vertex_Ctx   => Ctx.Vertex_Ctx,
            E_Loc        => N),
         V);

      CM.Insert (Union_Id (N), Trivial_Connection (V));
   end Do_Contract_Expression;

   --------------------------------
   -- Do_Simple_Return_Statement --
   --------------------------------

   procedure Do_Simple_Return_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V          : Flow_Graphs.Vertex_Id;
      Funcalls   : Call_Sets.Set;
      Indcalls   : Node_Sets.Set;
      Ret_Object : Entity_Id;

      Expr : constant Node_Id := Expression (N);

   begin
      if No (Expr) then
         --  We have a return for a procedure, entry, extended return or accept
         --  statement (Ada RM 6.5), however accept statements are not allowed
         --  in SPARK.

         if No (Ctx.Extended_Return) then
            Add_Vertex
              (FA,
               Direct_Mapping_Id (N),
               Make_Aux_Vertex_Attributes (E_Loc => N),
               V);

         --  This is a simple return statement within an extended return
         --  statement of a function.

         else
            pragma Assert (Ekind (FA.Spec_Entity) = E_Function);

            Ret_Object := Get_Return_Object (Ctx.Extended_Return);

            Add_Vertex
              (FA => FA,
               F  => Direct_Mapping_Id (N),
               A  =>
                 Make_Extended_Return_Attributes
                   (Var_Def         =>
                      Flatten_Variable (FA.Spec_Entity, FA.B_Scope),
                    Var_Use         =>
                      Flatten_Variable (Ret_Object, FA.B_Scope),
                    Object_Returned => Ret_Object,
                    Vertex_Ctx      => Ctx.Vertex_Ctx,
                    E_Loc           =>
                      Return_Statement_Entity (Ctx.Extended_Return)),
               V  => V);
         end if;
      else
         --  We have a function return
         Pick_Generated_Info
           (Expr,
            FA.B_Scope,
            Function_Calls     => Funcalls,
            Indirect_Calls     => Indcalls,
            Proof_Dependencies => FA.Proof_Dependencies,
            Tasking            => FA.Tasking,
            Generating_Globals => FA.Generating_Globals);

         Add_Vertex
           (FA,
            Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Var_Def    => Flatten_Variable (FA.Spec_Entity, FA.B_Scope),
               Var_Ex_Use =>
                 Get_Variables
                   (Expr,
                    Scope                => FA.B_Scope,
                    Target_Name          => Null_Flow_Id,
                    Fold_Functions       => Inputs,
                    Use_Computed_Globals => not FA.Generating_Globals),
               Subp_Calls => Funcalls,
               Indt_Calls => Indcalls,
               Vertex_Ctx => Ctx.Vertex_Ctx,
               E_Loc      => N),
            V);
         Ctx.Folded_Function_Checks.Append (Expr);
      end if;

      --  Control flows in, but we do not flow out again
      CM.Insert
        (Union_Id (N),
         Graph_Connections'(Standard_Entry => V, Standard_Exits => Empty_Set));

      --  When borrowers go out of scope, we pop them from the stack and
      --  assign back to the borrowed objects. This way we keep track of
      --  anything that happened while they were borrowed.

      for Decl of reverse Ctx.Borrowers loop
         Reclaim_Borrower (Decl, FA, Last => V);
      end loop;

      --  Instead we link the last vertex directly to the helper end vertex
      Linkup (FA, From => V, To => FA.Helper_End_Vertex);
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
      L     : Union_Lists.List := Union_Lists.Empty_List;
      Block : Graph_Connections;
      Decls : constant List_Id := Declarations (N);
      HSS   : constant Node_Id := Handled_Statement_Sequence (N);

      Borrowers_Marker : constant Ada.Containers.Count_Type :=
        Ctx.Borrowers.Length;
      --  Record current position of the borrows stack

   begin
      if Nkind (Original_Node (N)) in N_Subprogram_Call then
         Do_Null_Statement (N, FA, CM, Ctx);
         L.Append (Union_Id (N));
      end if;

      if Present (Decls) then
         Process_Statement_List (Decls, FA, CM, Ctx);
         L.Append (Union_Id (Decls));
      end if;

      --  When processing a package body respect the optional SPARK_Mode => Off
      --  on the package body statements.

      if (if Nkind (N) = N_Package_Body
          then Body_Statements_In_SPARK (Unique_Defining_Entity (N)))
      then
         Process_Statement (HSS, FA, CM, Ctx);
         L.Append (Union_Id (HSS));
      end if;

      Join (FA, CM, L, Block);

      --  When the subprogram or block exits early, e.g. with a RETURN or an
      --  EXIT statement, then we just forget about the borrowed objects. They
      --  have been already reclaimed when dealing with the exiting statement.

      if Block.Standard_Exits.Is_Empty then
         while Ctx.Borrowers.Length > Borrowers_Marker loop
            Ctx.Borrowers.Delete_Last;
         end loop;
      else
         declare
            V : Flow_Graphs.Vertex_Id;
            --  A dummy vertex which combines all the standard exits from
            --  the Handled_Statement_Sequence and has just one exit, so that
            --  the subsequent vertices which reclaim borrowers form just a
            --  straight single-entry -> single-exit sequence.

         begin
            Add_Vertex (FA, Null_Node_Attributes, V);

            Linkup (FA, Block.Standard_Exits, V);

            while Ctx.Borrowers.Length > Borrowers_Marker loop
               Reclaim_Borrower (Ctx.Borrowers.Last_Element, FA, Last => V);
               Ctx.Borrowers.Delete_Last;
            end loop;

            Block.Standard_Exits := Vertex_Sets.To_Set (V);
         end;
      end if;

      if Nkind (N) = N_Entry_Body then
         declare
            Formal_Part : constant Node_Id := Entry_Body_Formal_Part (N);
            Cond        : constant Node_Id := Condition (Formal_Part);

            V_C      : Flow_Graphs.Vertex_Id;
            V        : Flow_Graphs.Vertex_Id;
            Funcalls : Call_Sets.Set;
            Indcalls : Node_Sets.Set;

         begin
            Pick_Generated_Info
              (Cond,
               FA.B_Scope,
               Function_Calls     => Funcalls,
               Indirect_Calls     => Indcalls,
               Proof_Dependencies => FA.Proof_Dependencies,
               Tasking            => FA.Tasking,
               Generating_Globals => FA.Generating_Globals);

            Add_Vertex
              (FA,
               Direct_Mapping_Id (Cond),
               Make_Basic_Attributes
                 (Var_Ex_Use =>
                    Get_All_Variables
                      (Cond,
                       Scope                => FA.B_Scope,
                       Target_Name          => Null_Flow_Id,
                       Use_Computed_Globals => not FA.Generating_Globals),
                  Subp_Calls => Funcalls,
                  Indt_Calls => Indcalls,
                  Vertex_Ctx => Ctx.Vertex_Ctx,
                  E_Loc      => Cond,
                  Print_Hint => Pretty_Print_Entry_Barrier),
               V_C);
            --  Ctx.Folded_Function_Checks.Append (Cond);
            --  ??? O429-046 stitch actions?

            Add_Vertex
              (FA,
               Direct_Mapping_Id (Formal_Part),
               Make_Aux_Vertex_Attributes
                 (E_Loc => Formal_Part, Execution => Barrier),
               V);

            Linkup (FA, V_C, Block.Standard_Entry);
            Linkup (FA, V_C, V);

            Block.Standard_Entry := V_C;
            Block.Standard_Exits.Insert (V);
         end;
      end if;

      CM.Insert (Union_Id (N), Block);
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
      Typ : constant Entity_Id := Defining_Identifier (N);
   begin
      if Is_Scalar_Type (Typ) then
         declare
            R : constant Node_Id := Scalar_Range (Typ);

            Vars_Read : constant Flow_Id_Sets.Set :=
              Get_All_Variables
                (N                    => Low_Bound (R),
                 Scope                => FA.B_Scope,
                 Target_Name          => Null_Flow_Id,
                 Use_Computed_Globals => not FA.Generating_Globals)
              or Get_All_Variables
                   (N                    => High_Bound (R),
                    Scope                => FA.B_Scope,
                    Target_Name          => Null_Flow_Id,
                    Use_Computed_Globals => not FA.Generating_Globals);

            V : Flow_Graphs.Vertex_Id;
         begin
            Add_Vertex
              (FA,
               Direct_Mapping_Id (N),
               Make_Sink_Vertex_Attributes
                 (Vars_Read,
                  Is_Type_Decl => True,
                  Vertex_Ctx   => Ctx.Vertex_Ctx),
               V);
            CM.Insert (Union_Id (N), Trivial_Connection (V));
         end;
      else
         Add_Dummy_Vertex (N, FA, CM);
      end if;

      --  In phase 1, pull predicates and invariants that apply to type Typ
      --  into the proof dependencies of the unit.

      if FA.Generating_Globals and then Entity_In_SPARK (Typ) then
         Process_Type_Contracts (Typ, FA.B_Scope, True, FA.Proof_Dependencies);
      end if;

      --  In phase 2 check DIC on type definitions that come from source

      --  ??? As a rule, we shouldn't emit any messages while building the CFG.
      --  This check should be done as a dedicated analysis.

      if not FA.Generating_Globals
        and then Comes_From_Source (Typ)
        and then No (Full_View (Typ))
      then
         declare
            DIC_Promised : constant Boolean :=
              (Has_Own_DIC (Typ)
               and then Has_Fully_Default_Initializing_DIC_Pragma (Typ))
              or else (Is_Tagged_Type (Typ) and then Has_Inherited_DIC (Typ));
            --  Check both when there is a non-null DIC contract and when the
            --  DIC is inherited by the tagged type from its ancestor.

            pragma
              Assert
                (if Has_Own_DIC (Typ)
                     and then Has_Fully_Default_Initializing_DIC_Pragma (Typ)
                   then
                     Is_Default_Initialized
                       (Direct_Mapping_Id (Typ), Ignore_DIC => False));
            --  Sanity check: the type whose DIC we will examine should be
            --  recognized as default initialized from the outside (at least
            --  because of the DIC itself).

         begin
            if DIC_Promised
              and then not Is_Default_Initialized
                             (Direct_Mapping_Id (Typ), Ignore_DIC => True)
            then
               --  ??? For composite types we should pinpoint the exact
               --  component that renders the type not initialized by default.
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "type & is not fully initialized",
                  N        => N,
                  F1       => Direct_Mapping_Id (Typ),
                  Tag      => Default_Initialization_Mismatch,
                  Severity => Medium_Check_Kind);
            end if;
         end;
      end if;
   end Do_Type_Declaration;

   --------------------------------
   -- Process_Subprogram_Globals --
   --------------------------------

   procedure Process_Subprogram_Globals
     (Callsite : Node_Id;
      Ins      : in out Vertex_Lists.List;
      Outs     : in out Vertex_Lists.List;
      FA       : in out Flow_Analysis_Graphs;
      CM       : in out Connection_Maps.Map;
      Ctx      : in out Context)
   is
      pragma Unreferenced (CM);
      pragma Unmodified (Ctx);

      Globals : Global_Flow_Ids;
      V       : Flow_Graphs.Vertex_Id;
   begin
      --  Obtain globals (either from contracts or the computed stuff)
      Get_Globals
        (Subprogram          => Get_Called_Entity (Callsite),
         Scope               => FA.B_Scope,
         Classwide           => Flow_Classwide.Is_Dispatching_Call (Callsite),
         Globals             => Globals,
         Use_Deduced_Globals => not FA.Generating_Globals);

      --  User-written Inputs and Proof_Ins may include constants without
      --  variable input and we will complain about this when analyzying such
      --  contracts. Here we filter such constants to not propagate the user's
      --  mistake.
      Remove_Constants (Globals.Proof_Ins);
      Remove_Constants (Globals.Inputs);

      for R of Globals.Proof_Ins loop
         Add_Vertex
           (FA,
            Make_Global_Attributes
              (Callsite   => Callsite,
               Global     => R,
               Mode       => Mode_Proof,
               Scope      => FA.B_Scope,
               Vertex_Ctx => Ctx.Vertex_Ctx,
               E_Loc      => Callsite),
            V);
         Ins.Append (V);
      end loop;

      for R of Globals.Inputs loop
         Add_Vertex
           (FA,
            Make_Global_Attributes
              (Callsite   => Callsite,
               Global     => R,
               Mode       => Mode_In,
               Scope      => FA.B_Scope,
               Vertex_Ctx => Ctx.Vertex_Ctx,
               E_Loc      => Callsite),
            V);
         Ins.Append (V);
      end loop;

      for W of Globals.Outputs loop
         if not Globals.Inputs.Contains (Change_Variant (W, In_View)) then
            Add_Vertex
              (FA,
               Make_Global_Attributes
                 (Callsite   => Callsite,
                  Global     => Change_Variant (W, In_View),
                  Mode       => Mode_Out,
                  Scope      => FA.B_Scope,
                  Vertex_Ctx => Ctx.Vertex_Ctx,
                  E_Loc      => Callsite),
               V);
            Ins.Append (V);
         end if;
         Add_Vertex
           (FA,
            Make_Global_Attributes
              (Callsite   => Callsite,
               Global     => W,
               Mode       => Mode_Out,
               Scope      => FA.B_Scope,
               Vertex_Ctx => Ctx.Vertex_Ctx,
               E_Loc      => Callsite),
            V);
         Outs.Append (V);
      end loop;
   end Process_Subprogram_Globals;

   --------------------------
   -- Process_Call_Actuals --
   --------------------------

   procedure Process_Call_Actuals
     (Callsite            : Node_Id;
      Ins                 : in out Vertex_Lists.List;
      Outs_By_Copy        : in out Vertex_Lists.List;
      Outs_By_Reference   : in out Vertex_Lists.List;
      Outs_By_Unspecified : in out Vertex_Lists.List;
      FA                  : in out Flow_Analysis_Graphs;
      CM                  : in out Connection_Maps.Map;
      Ctx                 : in out Context)
   is
      pragma Unreferenced (CM);

      Called_Thing : constant Entity_Id := Get_Called_Entity (Callsite);

      procedure Handle_Parameter (Formal : Entity_Id; Actual : Node_Id)
      with
        Pre =>
          (if Is_Formal (Formal)
           then Nkind (Actual) in N_Subexpr
           elsif Is_Function_With_Side_Effects (Formal)
           then Nkind (Actual) in N_Subexpr | N_Defining_Identifier);

      ----------------------
      -- Handle_Parameter --
      ----------------------

      procedure Handle_Parameter (Formal : Entity_Id; Actual : Node_Id) is
         Funcalls : Call_Sets.Set;
         Indcalls : Node_Sets.Set;
         V        : Flow_Graphs.Vertex_Id;

      begin
         --  Build an in vertex
         Pick_Generated_Info
           (Actual,
            FA.B_Scope,
            Function_Calls     => Funcalls,
            Indirect_Calls     => Indcalls,
            Proof_Dependencies => FA.Proof_Dependencies,
            Tasking            => FA.Tasking,
            Generating_Globals => FA.Generating_Globals);

         Add_Vertex
           (FA,
            Direct_Mapping_Id (Actual, In_View),
            Make_Parameter_Attributes
              (FA         => FA,
               Callsite   => Callsite,
               Actual     => Actual,
               Formal     => Formal,
               In_Vertex  => True,
               Subp_Calls => Funcalls,
               Indt_Calls => Indcalls,
               Vertex_Ctx => Ctx.Vertex_Ctx,
               E_Loc      => Actual),
            V);

         if Nkind (Actual) in N_Subexpr then
            Ctx.Folded_Function_Checks.Append (Actual);
         else
            pragma Assert (Is_Function_With_Side_Effects (Formal));
         end if;
         Ins.Append (V);

         --  Build an out vertex
         if Ekind (Formal) in E_In_Out_Parameter | E_Out_Parameter | E_Function
           or else Is_Writable_Parameter (Formal)
         then
            Process_Reclamation_Functions
              (Etype (Formal), FA.Proof_Dependencies);

            Add_Vertex
              (FA,
               Direct_Mapping_Id (Actual, Out_View),
               Make_Parameter_Attributes
                 (FA         => FA,
                  Callsite   => Callsite,
                  Actual     => Actual,
                  Formal     => Formal,
                  In_Vertex  => False,
                  Vertex_Ctx => Ctx.Vertex_Ctx,
                  E_Loc      => Actual),
               V);

            if Is_Aliased (Formal)
              or else Is_By_Reference_Type (Etype (Formal))
              or else (Ekind (Formal) = E_In_Parameter
                       and then Is_Writable_Parameter (Formal))
            then
               Outs_By_Reference.Append (V);
            elsif Is_By_Copy_Type (Etype (Formal)) then
               Outs_By_Copy.Append (V);
            else
               Outs_By_Unspecified.Append (V);
            end if;
         end if;
      end Handle_Parameter;

      procedure Handle_Parameters is new
        Iterate_Call_Parameters (Handle_Parameter => Handle_Parameter);

      --  Start of processing for Process_Call_Actuals

   begin
      Handle_Parameters (Callsite);

      --  Function call is only processed for assignment where the call
      --  occurs immediately as the RHS and the function has side effects. The
      --  function entity acts as a formal parameter and the LHS acts as the
      --  actual parameter.

      if Nkind (Callsite) = N_Function_Call then
         declare
            Context : constant Node_Id := Parent (Callsite);
            Actual  : Node_Id;
         begin
            case Nkind (Context) is
               when N_Assignment_Statement =>
                  Actual := Name (Context);

               when N_Object_Declaration =>
                  Actual := Defining_Identifier (Context);

               when others =>
                  raise Program_Error;
            end case;
            Handle_Parameter
              (Formal => Get_Called_Entity (Callsite), Actual => Actual);
         end;
      end if;

      --  Create vertices for the implicit formal parameter
      if Ekind (Scope (Called_Thing)) = E_Protected_Type then
         if Is_External_Call (Callsite) then
            declare
               V : Flow_Graphs.Vertex_Id;

               Actual   : constant Node_Id := Prefix (Name (Callsite));
               Funcalls : Call_Sets.Set;
               Indcalls : Node_Sets.Set;

            begin
               --  Reading
               Pick_Generated_Info
                 (Actual,
                  FA.B_Scope,
                  Function_Calls     => Funcalls,
                  Indirect_Calls     => Indcalls,
                  Proof_Dependencies => FA.Proof_Dependencies,
                  Tasking            => FA.Tasking,
                  Generating_Globals => FA.Generating_Globals);

               Add_Vertex
                 (FA,
                  Direct_Mapping_Id (Actual, In_View),
                  Make_Implicit_Parameter_Attributes
                    (FA          => FA,
                     Call_Vertex => Callsite,
                     In_Vertex   => True,
                     Scope       => FA.B_Scope,
                     Subp_Calls  => Funcalls,
                     Indt_Calls  => Indcalls,
                     Vertex_Ctx  => Ctx.Vertex_Ctx,
                     E_Loc       => Callsite),
                  V);
               Ins.Append (V);

               --  Writing
               if Ekind (Called_Thing) /= E_Function then
                  Add_Vertex
                    (FA,
                     Direct_Mapping_Id (Actual, Out_View),
                     Make_Implicit_Parameter_Attributes
                       (FA          => FA,
                        Call_Vertex => Callsite,
                        In_Vertex   => False,
                        Scope       => FA.B_Scope,
                        Vertex_Ctx  => Ctx.Vertex_Ctx,
                        E_Loc       => Callsite),
                     V);
                  Outs_By_Reference.Append (V);
               end if;
            end;
         else
            declare
               V : Flow_Graphs.Vertex_Id;

            begin
               --  Reading
               Add_Vertex
                 (FA,
                  Make_Implicit_Parameter_Attributes
                    (FA          => FA,
                     Call_Vertex => Callsite,
                     In_Vertex   => True,
                     Scope       => FA.B_Scope,
                     Vertex_Ctx  => Ctx.Vertex_Ctx,
                     E_Loc       => Callsite),
                  V);
               Ins.Append (V);

               --  Writing
               if Ekind (Called_Thing) /= E_Function then
                  Add_Vertex
                    (FA,
                     Make_Implicit_Parameter_Attributes
                       (FA          => FA,
                        Call_Vertex => Callsite,
                        In_Vertex   => False,
                        Scope       => FA.B_Scope,
                        Vertex_Ctx  => Ctx.Vertex_Ctx,
                        E_Loc       => Callsite),
                     V);
                  Outs_By_Reference.Append (V);
               end if;
            end;
         end if;
      end if;
   end Process_Call_Actuals;

   ----------------------------
   -- Process_Statement_List --
   ----------------------------

   procedure Process_Statement_List
     (L   : List_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      P          : Node_Or_Entity_Id;
      Statements : Union_Lists.List := Union_Lists.Empty_List;
      Block      : Graph_Connections;
   begin
      --  Create initial nodes for the statements.
      P := First (L);
      while Present (P) loop
         case Nkind (P) is
            when Nodes_Ignored_By_Process_Statement =>
               --  We completely skip these.
               null;

            when others =>
               Process_Statement (P, FA, CM, Ctx);
               Statements.Append (Union_Id (P));

         end case;
         Next (P);
      end loop;

      --  Produce the joined up list.
      Join (FA => FA, CM => CM, Nodes => Statements, Block => Block);
      CM.Insert (Union_Id (L), Block);

   end Process_Statement_List;

   -----------------------
   -- Process_Statement --
   -----------------------

   procedure Process_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      L : Vertex_Lists.List;

      Folded_Functions_Marker : constant Ada.Containers.Count_Type :=
        Ctx.Folded_Function_Checks.Length;
      --  Record position of the folded functions stack

   begin
      Current_Error_Node := N;

      --  Deal with the statement.
      case Nkind (N) is
         when N_Assignment_Statement =>
            Do_Assignment_Statement (N, FA, CM, Ctx);

         when N_Block_Statement =>
            Do_Subprogram_Or_Block (N, FA, CM, Ctx);

         when N_Case_Statement =>
            Do_Case_Statement (N, FA, CM, Ctx);

         when N_Continue_Statement =>
            Do_Continue_Statement (N, FA, CM, Ctx);

         when N_Object_Declaration =>
            Do_Object_Declaration (N, FA, CM, Ctx);

         when N_Delay_Relative_Statement | N_Delay_Until_Statement =>
            Do_Delay_Statement (N, FA, CM, Ctx);

         when N_Entry_Call_Statement | N_Procedure_Call_Statement =>
            Do_Call_Statement (N, FA, CM, Ctx);

         when N_Exception_Declaration | N_Exception_Renaming_Declaration =>
            Do_Null_Statement (N, FA, CM, Ctx);

         when N_Exit_Statement =>
            Do_Exit_Statement (N, FA, CM, Ctx);

         when N_Extended_Return_Statement =>
            Do_Extended_Return_Statement (N, FA, CM, Ctx);

         when N_Full_Type_Declaration
            | N_Private_Extension_Declaration
            | N_Subtype_Declaration
         =>
            Do_Type_Declaration (N, FA, CM, Ctx);

         when N_Handled_Sequence_Of_Statements =>
            Do_Handled_Sequence_Of_Statements (N, FA, CM, Ctx);

         when N_If_Statement =>
            Do_If_Statement (N, FA, CM, Ctx);

         when N_Loop_Statement =>
            Do_Loop_Statement (N, FA, CM, Ctx);

         when N_Null_Statement =>
            Do_Null_Statement (N, FA, CM, Ctx);

         when N_Package_Body | N_Package_Body_Stub =>

            --  Skip bodies of generic packages and bodies of wrappers with
            --  instances of generic subprograms.

            declare
               E : constant Entity_Id := Unique_Defining_Entity (N);

            begin
               case Ekind (E) is
                  when E_Generic_Package =>
                     Add_Dummy_Vertex (N, FA, CM);

                  when E_Package =>
                     if Is_Wrapper_Package (E) then
                        Add_Dummy_Vertex (N, FA, CM);
                     else
                        Do_Package_Body_Or_Stub (N, FA, CM, Ctx);
                     end if;

                  when others =>
                     raise Program_Error;
               end case;
            end;

         when N_Package_Declaration =>
            Do_Package_Declaration (N, FA, CM, Ctx);

         when N_Pragma =>
            Do_Pragma (N, FA, CM, Ctx);

         when N_Raise_Statement =>
            Do_Raise_Statement (N, FA, CM, Ctx);

         when N_Raise_xxx_Error =>
            Do_Raise_xxx_Error (N, FA, CM, Ctx);

         when N_Simple_Return_Statement =>
            Do_Simple_Return_Statement (N, FA, CM, Ctx);

         when N_Goto_Statement =>
            Do_Goto_Statement (N, FA, CM, Ctx);

         when N_Label =>
            Do_Label (N, FA, CM, Ctx);

         when others =>
            Print_Node_Subtree (N);
            --  ??? To be added by various future tickets. Eventually we will
            --  replace this with a Why.Unexpected_Node exception.
            raise Why.Not_Implemented;

      end case;

      --  We chain the folded function checks in front of the actual vertex
      --  for this statement, if necessary. First we create a vertex for
      --  each expression we need to check.

      while Ctx.Folded_Function_Checks.Length > Folded_Functions_Marker loop
         declare
            Expr        : constant Node_Id :=
              Ctx.Folded_Function_Checks.Last_Element;
            Target_Name : constant Flow_Id :=
              (if Nkind (N) = N_Assignment_Statement
                 and then Has_Target_Names (N)
               then Path_To_Flow_Id (Name (N), FA.B_Scope)
               else Null_Flow_Id);

            Unchecked : Flow_Id_Sets.Set;

            V : Flow_Graphs.Vertex_Id;
         begin
            for Ref_Kind in Proof_Ins .. Null_Deps loop
               Unchecked :=
                 Get_Variables
                   (Expr,
                    Scope                => FA.B_Scope,
                    Target_Name          => Target_Name,
                    Fold_Functions       => Ref_Kind,
                    Use_Computed_Globals => not FA.Generating_Globals);

               if not Unchecked.Is_Empty then
                  Add_Vertex
                    (FA,
                     Make_Sink_Vertex_Attributes
                       (Var_Use       => Unchecked,
                        Is_Fold_Check => True,
                        Is_Assertion  => Ref_Kind = Proof_Ins,
                        Vertex_Ctx    => Ctx.Vertex_Ctx,
                        E_Loc         => Expr),
                     V);
                  L.Append (V);
               end if;
            end loop;

            Ctx.Folded_Function_Checks.Delete_Last;
         end;
      end loop;

      --  Then, if we created any new vertices we need to link them in front of
      --  the vertex created for N. We then re-adjust the standard entry for N.

      if not L.Is_Empty then
         L.Append (CM (Union_Id (N)).Standard_Entry);

         declare
            Prev : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
         begin
            for V of L loop
               if Prev /= Flow_Graphs.Null_Vertex then
                  Linkup (FA, Prev, V);
               end if;
               Prev := V;
            end loop;
         end;

         CM (Union_Id (N)).Standard_Entry := L.First_Element;
      end if;
   end Process_Statement;

   ----------------------
   -- Reclaim_Borrower --
   ----------------------

   procedure Reclaim_Borrower
     (Decl : Node_Id;
      FA   : in out Flow_Analysis_Graphs;
      Last : in out Flow_Graphs.Vertex_Id)
   is
      Borrower : constant Flow_Id :=
        Direct_Mapping_Id (Defining_Identifier (Decl));

      Borrowed : constant Flow_Id :=
        Path_To_Flow_Id
          (Get_Observed_Or_Borrowed_Expr (Expression (Decl)), FA.B_Scope);
      --  The borrower and borrowed objects, respectively

      V : Flow_Graphs.Vertex_Id;

   begin
      --  Add vertex for assigning the borrower back to the borrowed object and
      --  connect it with the graph.

      Add_Vertex
        (FA,
         Make_Basic_Attributes
           (Var_Def    => Flatten_Variable (Borrowed, FA.B_Scope),
            Var_Ex_Use => Flow_Id_Sets.To_Set (Borrower),
            Vertex_Ctx => No_Vertex_Context, --  ??? not sure about this
            Print_Hint => Pretty_Print_Reclaim,
            E_Loc      => Decl),
         V);
      FA.Atr (V).Is_Program_Node := False;

      Linkup (FA, From => Last, To => V);
      Last := V;
   end Reclaim_Borrower;

   ----------------------
   -- RHS_Split_Useful --
   ----------------------

   function RHS_Split_Useful
     (LHS : Node_Or_Entity_Id; RHS : Node_Id; Scope : Flow_Scope)
      return Boolean
   is

      function Is_Split_Useful (N : Node_Id) return Boolean
      with Pre => Nkind (N) in N_Subexpr;
      --  Returns True iff assignment with expression N should be analysed
      --  component-by-component.

      ---------------------
      -- Is_Split_Useful --
      ---------------------

      function Is_Split_Useful (N : Node_Id) return Boolean is
         T : constant Entity_Id := Get_Type (N, Scope);
      begin
         if not Is_Record_Type (T) then
            --  No point in trying to split if we are not dealing with some
            --  record type.
            return False;
         end if;

         --  Do not split N if objects of type T cannot be split
         declare
            F : constant Flow_Id := Direct_Mapping_Id (T);
            S : constant Flow_Id_Sets.Set := Get_Components (F, Scope);
         begin
            if S.Contains (F) then
               return False;
            end if;
         end;

         if not Is_Visible (T, Scope) then
            --  Sometimes we process things we're not really meant to see
            --  (such as private types in nested packages); in which case
            --  we should not split them. See OA14-027__flow_crash for a
            --  good example of this.
            return False;
         end if;

         case Nkind (N) is
            when N_Aggregate =>
               return not Is_Container_Aggregate (N);

            when N_Delta_Aggregate | N_Identifier | N_Expanded_Name =>
               return True;

            when N_Selected_Component =>
               return Is_Split_Useful (Prefix (N));

            when N_Attribute_Reference =>
               return
                 Attribute_Name (N) = Name_Update
                 and then Is_Split_Useful (Prefix (N));

            when N_Expression_With_Actions
               | N_Qualified_Expression
               | N_Type_Conversion
            =>
               return Is_Split_Useful (Expression (N));

            when others =>
               return False;
         end case;
      end Is_Split_Useful;

      LHS_Root : constant Entity_Id :=
        (if Nkind (LHS) in N_Subexpr then Get_Root_Object (LHS) else LHS);

      --  Start of processing for RHS_Split_Useful

   begin
      --  If LHS denotes an overlaid entity, there is no point in splitting the
      --  RHS into components.

      if Ekind (LHS_Root) in E_Constant | E_Variable
        and then Present (Ultimate_Overlaid_Entity (LHS_Root))
      then
         return False;
      end if;

      return Is_Split_Useful (RHS);
   end RHS_Split_Useful;

   ----------------------------
   -- Mark_Exceptional_Paths --
   ----------------------------

   procedure Mark_Exceptional_Paths (FA : in out Flow_Analysis_Graphs) is
      --  Identification of exceptional paths is a bit tedious. We use a number
      --  of simple DFS passes over the graph which will eventually flag all
      --  vertices belonging to exceptional paths or dead code.
      --
      --  1. We need to detect dead code (which is again later detected by
      --     flow-analysis). We flag all vertices that are not identified here.
      --
      --  2. We then note which vertices can be reached in a reversed DFS
      --     search (but not crossing ABEND edges) - all remaining vertices are
      --     necessarily exceptional.
      --
      --  3. We need to account for dead code in exceptional paths; we perform
      --     another dead code detection but this time we don't cross
      --     exceptional path vertices in the DFS. We flag all vertices
      --     identified here.
      --
      --  4. Finally, when we prune exceptional paths we might leave an if
      --     statement with only a single exit: such a vertex consumes
      --     variables but has no effect on the program. We set
      --     Is_Exceptional_Branch on these vertices so we can ignore them in
      --     flow-analysis.

      Pathable : Vertex_Sets.Set := Vertex_Sets.Empty_Set;  -- Step 1
      Live     : Vertex_Sets.Set := Vertex_Sets.Empty_Set;  -- Step 2
      Dead     : Vertex_Sets.Set;                           -- Step 3

      function Ignore_Abend_Edges
        (A, B : Flow_Graphs.Vertex_Id) return Boolean;
      --  Traverses all edges except ABEND edges

      procedure Mark_Pathable
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction);
      --  Used in step 1 to populate `Pathable'

      procedure Mark_Live
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction);
      --  Used in step 2 to populate `Live'

      procedure Mark_Dead
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction);
      --  Used in step 2 to set Is_Exceptional_Path

      procedure Mark_Reachable
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction);
      --  Used in step 3 to reduce `Dead'

      ------------------------
      -- Ignore_Abend_Edges --
      ------------------------

      function Ignore_Abend_Edges (A, B : Flow_Graphs.Vertex_Id) return Boolean
      is
      begin
         case FA.CFG.Edge_Colour (A, B) is
            when EC_Default | EC_Barrier | EC_Inf =>
               return True;

            when EC_Abend =>
               return False;

            when others =>
               raise Program_Error;
         end case;
      end Ignore_Abend_Edges;

      -------------------
      -- Mark_Pathable --
      -------------------

      procedure Mark_Pathable
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction) is
      begin
         Pathable.Insert (V);
         if V = FA.End_Vertex then
            TV := Flow_Graphs.Skip_Children;
         else
            TV := Flow_Graphs.Continue;
         end if;
      end Mark_Pathable;

      ---------------
      -- Mark_Live --
      ---------------

      procedure Mark_Live
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction) is
      begin
         if V = FA.Start_Vertex then
            TV := Flow_Graphs.Skip_Children;
         else
            Live.Insert (V);
            TV := Flow_Graphs.Continue;
         end if;
      end Mark_Live;

      ---------------
      -- Mark_Dead --
      ---------------

      procedure Mark_Dead
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction) is
      begin
         if V = FA.End_Vertex then
            TV := Flow_Graphs.Skip_Children;
         else
            if not Live.Contains (V) then
               FA.Atr (V).Is_Exceptional_Path := True;
            end if;
            TV := Flow_Graphs.Continue;
         end if;
      end Mark_Dead;

      --------------------
      -- Mark_Reachable --
      --------------------

      procedure Mark_Reachable
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction) is
      begin
         Dead.Exclude (V);
         if V = FA.End_Vertex or else FA.Atr (V).Is_Exceptional_Path then
            TV := Flow_Graphs.Skip_Children;
         else
            TV := Flow_Graphs.Continue;
         end if;
      end Mark_Reachable;

      --  Start of processing for Mark_Exceptional_Paths

   begin
      --  (1) Detect all non-dead-code vertices and place them in set
      --      `Pathable'.
      FA.CFG.DFS
        (Start         => FA.Start_Vertex,
         Include_Start => True,
         Visitor       => Mark_Pathable'Access,
         Edge_Selector => Ignore_Abend_Edges'Access);

      --  (1) Flag all dead-code vertices
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : V_Attributes renames FA.Atr (V);

         begin

            --  Ignore vertices that were flagged as live

            if Pathable.Contains (V) then
               null;

            --  Ignore the end vertex

            elsif V = FA.End_Vertex then
               null;

            --  Ignore 'Initial and 'Final vertices

            elsif FA.CFG.Get_Key (V).Variant in Initial_Value .. Final_Grouping
            then
               null;

            --  Ignore vertices whose attributes are Null_Node_Attributes

            elsif Atr.Is_Null_Node and then Atr.Is_Program_Node then
               null;

            --  Flag the remaining vertices

            else
               --  Here, we store the value of Is_Program_Node in
               --  Is_Original_Program_Node because we want to raise
               --  warnings about unreachable nodes in Find_Dead_Code.
               Atr.Is_Original_Program_Node := Atr.Is_Program_Node;
               Atr.Is_Dead_Path := True;
            end if;
         end;
      end loop;

      --  (2) In reverse, find reachable nodes (not crossing ABEND edges) and
      --      place them in set `Live'.
      FA.CFG.DFS
        (Start         => FA.End_Vertex,
         Include_Start => False,
         Visitor       => Mark_Live'Access,
         Edge_Selector => Ignore_Abend_Edges'Access,
         Reversed      => True);

      --  (2) From start, flag all vertices reachable but not in set `Live'
      FA.CFG.DFS
        (Start         => FA.Start_Vertex,
         Include_Start => False,
         Visitor       => Mark_Dead'Access);

      --  (3) From start, remove all vertices reachable from set `Dead' (not
      --      crossing ABEND edges or exceptional paths).
      Dead := Live;
      FA.CFG.DFS
        (Start         => FA.Start_Vertex,
         Include_Start => False,
         Visitor       => Mark_Reachable'Access,
         Edge_Selector => Ignore_Abend_Edges'Access);

      --  (3) Flag all vertices of Dead
      for V of Dead loop

         --  Here, we don't store Is_Program_Node in Is_Original_Program_Node
         --  because the code is not actually unreachable, and we don't want
         --  to raise warnings on those vertices.
         FA.Atr (V).Is_Exceptional_Path := True;
      end loop;

      --  (4) Flag all vertices that have an exceptional path as an out
      --      neighbour.
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         if FA.Atr (V).Is_Exceptional_Path then
            for N of FA.CFG.Get_Collection (V, Flow_Graphs.In_Neighbours) loop
               declare
                  Atr_N : V_Attributes renames FA.Atr (N);
               begin
                  if not Atr_N.Is_Exceptional_Path then
                     Atr_N.Is_Exceptional_Branch := True;
                  end if;
               end;
            end loop;
         end if;
      end loop;
   end Mark_Exceptional_Paths;

   ----------------------
   -- Prune_Dead_Paths --
   ----------------------

   procedure Prune_Dead_Paths (FA : in out Flow_Analysis_Graphs) is
   begin
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : V_Attributes renames FA.Atr (V);

         begin
            if Atr.Is_Dead_Path then

               --  If we are dealing with a declaration node, then we delete
               --  the corresponding 'Initial and 'Final vertices as well.
               if Atr.Is_Declaration_Node then
                  for F of Atr.Variables_Defined loop
                     Clear_Vertex_And_Attributes
                       (FA,
                        FA.CFG.Get_Vertex (Change_Variant (F, Initial_Value)));
                     Clear_Vertex_And_Attributes
                       (FA,
                        FA.CFG.Get_Vertex (Change_Variant (F, Final_Value)));
                  end loop;
               end if;

               --  Then we delete vertex V
               Clear_Vertex_And_Attributes (FA, V);
            end if;
         end;
      end loop;
   end Prune_Dead_Paths;

   -----------------------------
   -- Prune_Exceptional_Paths --
   -----------------------------

   procedure Prune_Exceptional_Paths (FA : in out Flow_Analysis_Graphs) is
   begin
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : V_Attributes renames FA.Atr (V);

         begin
            if Atr.Is_Exceptional_Path then

               --  If we are dealing with a declaration node, then we delete
               --  the corresponding 'Initial and 'Final vertices as well.
               if Atr.Is_Declaration_Node then
                  for F of Atr.Variables_Defined loop
                     Clear_Vertex_And_Attributes
                       (FA,
                        FA.CFG.Get_Vertex (Change_Variant (F, Initial_Value)));
                     Clear_Vertex_And_Attributes
                       (FA,
                        FA.CFG.Get_Vertex (Change_Variant (F, Final_Value)));
                  end loop;
               end if;

               --  Then we delete vertex V
               Clear_Vertex_And_Attributes (FA, V);
            end if;
         end;
      end loop;

      --  Sometimes a subprogram is entirely exceptional. In this case we
      --  need to make sure we can still reach the final vertex.
      if not FA.CFG.Non_Trivial_Path_Exists (FA.Start_Vertex, FA.End_Vertex)
      then
         if not FA.Generating_Globals
           and then FA.Kind = Kind_Subprogram
           and then not No_Return (FA.Spec_Entity)
         then
            --  We warn about this, but only for subprograms not
            --  annotated with No_Return.
            Error_Msg_Flow
              (FA       => FA,
               Msg      =>
                 "all paths in & raise exceptions "
                 & "or do not terminate normally",
               N        => FA.Spec_Entity,
               Severity => High_Check_Kind,
               Tag      => Missing_Return,
               F1       => Direct_Mapping_Id (FA.Spec_Entity));
            FA.Has_Only_Exceptional_Paths := True;
         end if;
         FA.CFG.Add_Edge (FA.Start_Vertex, FA.End_Vertex, EC_Default);
      end if;
   end Prune_Exceptional_Paths;

   -------------------------
   -- Separate_Dead_Paths --
   -------------------------

   procedure Separate_Dead_Paths (FA : in out Flow_Analysis_Graphs) is
      Live : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
      Dead : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

      procedure Mark_Live
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction);
      --  Populate `Live'.

      procedure Mark_Dead
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction);
      --  Populate `Dead' with all vertices not explicitly live.

      ---------------
      -- Mark_Live --
      ---------------

      procedure Mark_Live
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction) is
      begin
         Live.Insert (V);
         if V = FA.End_Vertex then
            TV := Flow_Graphs.Skip_Children;
         else
            TV := Flow_Graphs.Continue;
         end if;
      end Mark_Live;

      ---------------
      -- Mark_Dead --
      ---------------

      procedure Mark_Dead
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction) is
      begin
         if not Live.Contains (V) then
            Dead.Insert (V);
            TV := Flow_Graphs.Skip_Children;
         elsif V = FA.Start_Vertex then
            TV := Flow_Graphs.Skip_Children;
         else
            TV := Flow_Graphs.Continue;
         end if;
      end Mark_Dead;

      --  Start of processing for Separate_Dead_Paths

   begin
      FA.CFG.DFS
        (Start         => FA.Start_Vertex,
         Include_Start => True,
         Visitor       => Mark_Live'Access);

      FA.CFG.DFS
        (Start         => FA.End_Vertex,
         Include_Start => True,
         Visitor       => Mark_Dead'Access,
         Reversed      => True);

      for Dead_V of Dead loop
         declare
            Live_Neighbours : Vertex_Lists.List;
         begin
            for V of FA.CFG.Get_Collection (Dead_V, Flow_Graphs.Out_Neighbours)
            loop
               if Live.Contains (V) then
                  Live_Neighbours.Append (V);
               end if;
            end loop;
            for Live_V of Live_Neighbours loop
               FA.CFG.Remove_Edge (Dead_V, Live_V);
            end loop;
         end;
      end loop;
   end Separate_Dead_Paths;

   ------------------
   -- Simplify_CFG --
   ------------------

   procedure Simplify_CFG (FA : in out Flow_Analysis_Graphs) is
   begin
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : V_Attributes renames FA.Atr (V);

         begin
            if Atr.Is_Null_Node then
               --  Sanity-check: null vertices should not be flagged as
               --  neverending and simplified.

               pragma Assert (not Atr.Is_Neverending);

               --  Close the subgraph indicated by V's neighbours
               for A of FA.CFG.Get_Collection (V, Flow_Graphs.In_Neighbours)
               loop
                  for B of
                    FA.CFG.Get_Collection (V, Flow_Graphs.Out_Neighbours)
                  loop
                     --  The colour edges depends on the source vertex; for
                     --  edges incoming to the null vertex this colour can
                     --  be anything and it must be preserved.

                     FA.CFG.Add_Edge (A, B, FA.CFG.Edge_Colour (A, V));

                     --  The colour of edges outgoing from a null vertex is
                     --  always "default"; such edges can be safely ignored.

                     pragma Assert (FA.CFG.Edge_Colour (V, B) = EC_Default);
                  end loop;
               end loop;

               --  Remove all edges from the vertex and clear the node
               Clear_Vertex_And_Attributes (FA, V);
            end if;
         end;
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

         --  Do not issue a warning on invariant pragmas, as one is already
         --  issued on the corresponding type in SPARK.Definition.

         when Pragma_Invariant
            | Pragma_Type_Invariant
            | Pragma_Type_Invariant_Class
         =>
            return False;

         --  Remaining pragmas fall into two major groups:
         --
         --  Group 1 - ignored
         --
         --  Pragmas that do not need any marking, either because:
         --  . they are defined by SPARK 2014, or
         --  . they are already taken into account elsewhere (contracts)
         --  . they have no effect on control flow graphs

         --  Group 1a - RM Table 16.1, Ada language-defined pragmas marked
         --  "Yes".

         when  --  Pragma_Assert is transformed into pragma Check handled above
            Pragma_Assertion_Policy
            | Pragma_Atomic
            | Pragma_Atomic_Components
            | Pragma_Attach_Handler
            | Pragma_Convention
            | Pragma_CPU
            | Pragma_Detect_Blocking
            | Pragma_Elaborate
            | Pragma_Elaborate_All
            | Pragma_Elaborate_Body
            | Pragma_Export
            | Pragma_Import
            | Pragma_Independent
            | Pragma_Independent_Components
            | Pragma_Inline
            | Pragma_Inspection_Point
            | Pragma_Interrupt_Handler
            | Pragma_Interrupt_Priority
            | Pragma_Linker_Options
            | Pragma_List
            | Pragma_Locking_Policy
            | Pragma_No_Return
            | Pragma_Normalize_Scalars
            | Pragma_Optimize
            | Pragma_Pack
            | Pragma_Page
            | Pragma_Partition_Elaboration_Policy
            | Pragma_Preelaborable_Initialization
            | Pragma_Preelaborate
            | Pragma_Priority
            | Pragma_Profile
            | Pragma_Pure
            | Pragma_Queuing_Policy
            | Pragma_Relative_Deadline
            | Pragma_Restrictions
            | Pragma_Reviewable
            | Pragma_Suppress
            | Pragma_Unchecked_Union
            | Pragma_Unsuppress
            | Pragma_Volatile
            | Pragma_Volatile_Components

            --  Group 1b - RM Table 16.2, SPARK language-defined pragmas marked
            --  "Yes", whose effect on flow analysis is taken care of somewhere
            --  else.

            | Pragma_Abstract_State
            --  Pragma_Assert_And_Cut and Pragma_Assume are transformed into
            --  pragma Check handled above.
            | Pragma_Async_Readers
            | Pragma_Async_Writers
            | Pragma_Constant_After_Elaboration
            | Pragma_Contract_Cases
            | Pragma_Default_Initial_Condition
            | Pragma_Depends
            | Pragma_Effective_Reads
            | Pragma_Effective_Writes
            | Pragma_Extensions_Visible  --  ??? possible improvement NA03-003
            | Pragma_Ghost
            | Pragma_Global
            | Pragma_Initial_Condition
            | Pragma_Initializes
            --  Pragma_Loop_Invariant is transformed into pragma Check
            --  handled above.
            --  Pragma_Loop_Variant is handled specially above
            | Pragma_No_Caching
            | Pragma_Part_Of
            | Pragma_Refined_Depends
            | Pragma_Refined_Global
            | Pragma_Refined_Post
            | Pragma_Refined_State
            | Pragma_SPARK_Mode
            | Pragma_Unevaluated_Use_Of_Old
            | Pragma_Volatile_Function

            --  Group 1c - RM Table 16.3, GNAT implementation-defined pragmas
            --  marked "Yes".

            | Pragma_Ada_83
            | Pragma_Ada_95
            | Pragma_Ada_05
            | Pragma_Ada_12
            | Pragma_Ada_2005
            | Pragma_Ada_2012
            | Pragma_Ada_2022
            | Pragma_Annotate
            | Pragma_Assume_No_Invalid_Values
            --  Pragma_Check is handled specially above
            | Pragma_Check_Policy
            --  Pragma_Compile_Time_Error, Pragma_Compile_Time_Warning and
            --  Pragma_Debug are removed by FE and handled thus below.
            | Pragma_Default_Scalar_Storage_Order
            | Pragma_Export_Function
            | Pragma_Export_Procedure
            | Pragma_Ignore_Pragma
            | Pragma_Inline_Always
            --  Pragma_Invariant is handled specially above
            | Pragma_Linker_Section
            | Pragma_Max_Queue_Length
            | Pragma_No_Elaboration_Code_All
            | Pragma_No_Heap_Finalization
            | Pragma_No_Inline
            | Pragma_No_Tagged_Streams
            | Pragma_Overflow_Mode
            | Pragma_Post
            | Pragma_Postcondition
            | Pragma_Post_Class
            | Pragma_Pre
            | Pragma_Precondition
            | Pragma_Pre_Class
            | Pragma_Predicate
            | Pragma_Predicate_Failure
            | Pragma_Provide_Shift_Operators
            | Pragma_Pure_Function
            | Pragma_Restriction_Warnings
            | Pragma_Secondary_Stack_Size
            | Pragma_Style_Checks
            | Pragma_Test_Case
            --  Pragma_Type_Invariant and Pragma_Type_Invariant_Class are
            --  handled specially above.
            | Pragma_Unmodified
            | Pragma_Unreferenced
            | Pragma_Unused
            | Pragma_Validity_Checks
            | Pragma_Volatile_Full_Access
            | Pragma_Warnings
            | Pragma_Weak_External
         =>
            return False;

         --  Group 1d - These pragmas are re-written and/or removed by the
         --  front-end in GNATprove, so they should never be seen here,
         --  unless they are ignored by virtue of pragma Ignore_Pragma.

         when Pragma_Assert
            | Pragma_Assert_And_Cut
            | Pragma_Assume
            | Pragma_Compile_Time_Error
            | Pragma_Compile_Time_Warning
            | Pragma_Debug
            | Pragma_Loop_Invariant
         =>
            return False;

         --  Group 2 - Remaining pragmas, enumerated here rather than a
         --  "when others" to force re-consideration when SNames.Pragma_Id
         --  is extended.
         --
         --  These can all be ignored - we already generated a warning during
         --  Marking. In future, these pragmas may move to be fully ignored or
         --  to be processed with more semantic detail as required.

         --  Group 2a - GNAT Defined and obsolete pragmas

         when Pragma_Abort_Defer
            | Pragma_Allow_Integer_Address
            | Pragma_Attribute_Definition
            | Pragma_C_Pass_By_Copy
            | Pragma_Check_Float_Overflow
            | Pragma_Check_Name
            | Pragma_Comment
            | Pragma_Common_Object
            | Pragma_Complete_Representation
            | Pragma_Complex_Representation
            | Pragma_Component_Alignment
            | Pragma_Controlled
            | Pragma_Convention_Identifier
            | Pragma_CPP_Class
            | Pragma_CPP_Constructor
            | Pragma_CPP_Virtual
            | Pragma_CPP_Vtable
            | Pragma_Debug_Policy
            | Pragma_Default_Storage_Pool
            | Pragma_Disable_Atomic_Synchronization
            | Pragma_Dispatching_Domain
            | Pragma_Elaboration_Checks
            | Pragma_Eliminate
            | Pragma_Enable_Atomic_Synchronization
            | Pragma_Export_Object
            | Pragma_Export_Valued_Procedure
            | Pragma_Extend_System
            | Pragma_Extensions_Allowed
            | Pragma_External
            | Pragma_External_Name_Casing
            | Pragma_Fast_Math
            | Pragma_Favor_Top_Level
            | Pragma_Finalize_Storage_Only
            | Pragma_Ident
            | Pragma_Implementation_Defined
            | Pragma_Implemented
            | Pragma_Implicit_Packing
            | Pragma_Import_Function
            | Pragma_Import_Object
            | Pragma_Import_Procedure
            | Pragma_Import_Valued_Procedure
            | Pragma_Initialize_Scalars
            | Pragma_Inline_Generic
            | Pragma_Interface
            | Pragma_Interface_Name
            | Pragma_Interrupt_State
            | Pragma_Keep_Names
            | Pragma_License
            | Pragma_Link_With
            | Pragma_Linker_Alias
            | Pragma_Linker_Constructor
            | Pragma_Linker_Destructor
            | Pragma_Loop_Optimize
            | Pragma_Machine_Attribute
            | Pragma_Main
            | Pragma_Main_Storage
            | Pragma_Memory_Size
            | Pragma_No_Body
            | Pragma_No_Run_Time
            | Pragma_No_Strict_Aliasing
            | Pragma_Obsolescent
            | Pragma_Optimize_Alignment
            | Pragma_Ordered
            | Pragma_Overriding_Renamings
            | Pragma_Passive
            | Pragma_Persistent_BSS
            | Pragma_Prefix_Exception_Messages
            | Pragma_Priority_Specific_Dispatching
            | Pragma_Profile_Warnings
            | Pragma_Propagate_Exceptions
            | Pragma_Psect_Object
            | Pragma_Rational
            | Pragma_Ravenscar
            | Pragma_Remote_Access_Type
            | Pragma_Rename_Pragma
            | Pragma_Restricted_Run_Time
            | Pragma_Share_Generic
            | Pragma_Shared
            | Pragma_Short_Circuit_And_Or
            | Pragma_Short_Descriptors
            | Pragma_Simple_Storage_Pool_Type
            | Pragma_Source_File_Name
            | Pragma_Source_File_Name_Project
            | Pragma_Source_Reference
            | Pragma_Static_Elaboration_Desired
            | Pragma_Storage_Unit
            | Pragma_Stream_Convert
            | Pragma_Subtitle
            | Pragma_Suppress_All
            | Pragma_Suppress_Debug_Info
            | Pragma_Suppress_Exception_Locations
            | Pragma_Suppress_Initialization
            | Pragma_System_Name
            | Pragma_Task_Info
            | Pragma_Task_Name
            | Pragma_Task_Storage
            | Pragma_Thread_Local_Storage
            | Pragma_Time_Slice
            | Pragma_Title
            | Pragma_Unimplemented_Unit
            | Pragma_Universal_Aliasing
            | Pragma_Unreferenced_Objects
            | Pragma_Unreserve_All_Interrupts
            | Pragma_Use_VADS_Size
            | Pragma_Warning_As_Error
            | Pragma_Wide_Character_Encoding

            --  Group 2b - Ada RM pragmas
            | Pragma_Discard_Names
            | Pragma_Task_Dispatching_Policy
            | Pragma_All_Calls_Remote
            | Pragma_Asynchronous
            | Pragma_Remote_Call_Interface
            | Pragma_Remote_Types
            | Pragma_Shared_Passive
            | Pragma_Lock_Free
            | Pragma_Storage_Size
         =>
            return False;

         --  Unknown_Pragma is treated here. We use an OTHERS case in order to
         --  deal with all the more recent pragmas introduced in GNAT for which
         --  we have not yet defined how they are supported in SPARK. Do not
         --  issue a warning on unknown pragmas, as an error is issued in
         --  SPARK.Definition.

         when others =>
            return False;
      end case;

   end Pragma_Relevant_To_Flow;

   ---------------------------
   -- Register_Own_Variable --
   ---------------------------

   procedure Register_Own_Variable
     (FA : in out Flow_Analysis_Graphs; E : Entity_Id) is
   begin
      if FA.Generating_Globals
        and then FA.Kind = Kind_Package
        and then (FA.Is_Generative or else Is_Child_Unit (FA.Spec_Entity))
        and then Is_Package_State (E)
      then
         FA.GG.Local_Variables.Insert (E);
      end if;
   end Register_Own_Variable;

   ------------------------------------------------------------
   --  Package functions and procedures
   ------------------------------------------------------------

   ----------------------
   -- Clear_Attributes --
   ----------------------

   procedure Clear_Vertex_And_Attributes
     (FA : in out Flow_Analysis_Graphs; V : Flow_Graphs.Vertex_Id)
   is
      Atr : V_Attributes renames FA.Atr (V);
   begin
      FA.CFG.Clear_Vertex (V);
      Atr :=
        (Null_Attributes
         with delta
           Is_Null_Node             => True,
           Is_Dead_Path             => Atr.Is_Dead_Path,
           Is_Original_Program_Node => Atr.Is_Original_Program_Node,
           Error_Location           => Atr.Error_Location,
           Warnings_Off             => Atr.Warnings_Off);
   end Clear_Vertex_And_Attributes;

   ------------
   -- Create --
   ------------

   procedure Create (FA : in out Flow_Analysis_Graphs) is
      Connection_Map    : Connection_Maps.Map := Connection_Maps.Empty_Map;
      The_Context       : Context := No_Context;
      Init_Block        : Graph_Connections;
      Precon_Block      : Graph_Connections;
      Postcon_Block     : Graph_Connections;
      Excep_Cases_Block : Graph_Connections;
      Body_N            : Node_Id;
      Spec_N            : Node_Id;

   begin
      case FA.Kind is
         when Kind_Subprogram | Kind_Task =>
            Body_N := Get_Body (FA.Spec_Entity);

         when Kind_Package =>
            Spec_N := Package_Specification (FA.Spec_Entity);
            Body_N :=
              (if Entity_Body_In_SPARK (FA.Spec_Entity)
               then Package_Body (FA.Spec_Entity)
               else Spec_N);

      end case;

      --  Create the magic start, helper end and end vertices
      --
      --  The start vertex has the entity's location, because it is
      --  convenient place to put error messages that apply to the
      --  whole subprogram/package/body.
      Add_Vertex
        (FA,
         (Null_Attributes with delta Error_Location => Body_N),
         FA.Start_Vertex);
      Add_Vertex (FA, Null_Attributes, FA.Helper_End_Vertex);
      Add_Vertex (FA, Null_Attributes, FA.Exceptional_End_Vertex);
      Add_Vertex (FA, Null_Attributes, FA.End_Vertex);

      --  Create the magic null export vertices: initial and final, and
      --  recognize it as a known variable.
      for Variant in Initial_Value .. Final_Value loop
         declare
            F : constant Flow_Id :=
              Change_Variant (Null_Export_Flow_Id, Variant);
         begin
            Add_Vertex (FA, F, Make_Null_Export_Attributes (F));
         end;
      end loop;

      FA.All_Vars.Insert (Null_Export_Flow_Id);

      --  Create initial and final vertices for the parameters of the analyzed
      --  entity, and pull the proof dependencies from their types. Type
      --  invariants from the enclosing unit are pulled only when the entity
      --  is a boundary subprogram.
      case FA.Kind is
         when Kind_Subprogram =>
            for Param of Get_Formals (FA.Spec_Entity) loop
               Create_Initial_And_Final_Vertices (Param, FA);
               Process_Type_Contracts
                 (Etype (Param),
                  FA.B_Scope,
                  Is_Globally_Visible (FA.Spec_Entity),
                  FA.Proof_Dependencies);
            end loop;

         when Kind_Task =>
            --  Tasks see themselves as formal "in out" parameters
            --
            --  This includes, after flattening:
            --    * variables that are Part_Of tasks,
            --    * discriminants of tasks (but these are only considered to be
            --      formal in parameters)
            Create_Initial_And_Final_Vertices (FA.Spec_Entity, FA);

         when Kind_Package =>
            null;
      end case;

      --  Collect globals for the analyzed entity and create initial and final
      --  vertices.
      if not FA.Generating_Globals then
         case FA.Kind is
            when Kind_Subprogram | Kind_Task =>
               declare
                  Globals : Global_Flow_Ids;

               begin
                  Get_Globals
                    (Subprogram => FA.Spec_Entity,
                     Scope      => FA.B_Scope,
                     Classwide  => False,
                     Globals    => Globals);

                  --  Convert globals from the In_View/Out_View to Normal_Use
                  --  variants to simplify splitting Inputs and Outputs into
                  --  In/In_Out/Out globals.

                  Globals :=
                    (Proof_Ins =>
                       Change_Variant (Globals.Proof_Ins, Normal_Use),
                     Inputs    => Change_Variant (Globals.Inputs, Normal_Use),
                     Outputs   =>
                       Change_Variant (Globals.Outputs, Normal_Use));

                  for G of Globals.Proof_Ins loop
                     Create_Initial_And_Final_Vertices (G, Mode_Proof, FA);
                  end loop;

                  for G of Globals.Inputs.Difference (Globals.Outputs) loop
                     Create_Initial_And_Final_Vertices (G, Mode_In, FA);
                  end loop;

                  for G of Globals.Outputs.Difference (Globals.Inputs) loop
                     Create_Initial_And_Final_Vertices (G, Mode_Out, FA);
                  end loop;

                  for G of Globals.Inputs.Intersection (Globals.Outputs) loop
                     Create_Initial_And_Final_Vertices (G, Mode_In_Out, FA);
                  end loop;
               end;

            when Kind_Package =>
               --  Packages have no obvious globals, but we can extract a list
               --  of global variables used from the optional rhs of the
               --  initializes clause:
               --
               --     Initializes => (State => (Global_A, ...),
               --
               --  Any other use of non-local variables is not legal, see SRM
               --  7.1.5(11).
               --
               --  Such globals are global inputs *only*, as packages are only
               --  allowed to initialize their own state.
               declare
                  Inputs_Seen : Flow_Id_Sets.Set;
                  --  An entity might occur on several RHS of Initializes
                  --  aspect; with this set we avoid duplicates.

                  Unused   : Flow_Id_Sets.Cursor;
                  Inserted : Boolean;

                  DM : constant Dependency_Maps.Map :=
                    Parse_Initializes (FA.Spec_Entity, FA.S_Scope);

               begin
                  for C in DM.Iterate loop
                     declare
                        The_Ins : Flow_Id_Sets.Set renames DM (C);
                     begin
                        for Input of Down_Project (The_Ins, FA.B_Scope) loop
                           Inputs_Seen.Insert
                             (New_Item => Input,
                              Position => Unused,
                              Inserted => Inserted);

                           if Inserted then
                              Create_Initial_And_Final_Vertices
                                (F => Input, Mode => Mode_In, FA => FA);
                           end if;
                        end loop;
                     end;
                  end loop;
               end;

               --  If a Refined_State aspect exists then create initial and
               --  final vertices for constituents declared in other (private
               --  child) units.

               if Entity_Body_In_SPARK (FA.Spec_Entity)
                 and then Has_Non_Null_Abstract_State (FA.Spec_Entity)
               then
                  for State of Iter (Abstract_States (FA.Spec_Entity)) loop
                     if not Has_Null_Refinement (State) then
                        for Constituent of
                          Iter (Refinement_Constituents (State))
                        loop
                           if not Entity_Is_In_Main_Unit (Constituent) then
                              --  ??? we should also set Is_Export flag, just
                              --  like when processing constituents from the
                              --  same unit.

                              Create_Initial_And_Final_Vertices
                                (E => Constituent, FA => FA);
                           end if;
                        end loop;
                     end if;
                  end loop;
               end if;
         end case;
      end if;

      --  If we are dealing with a function, we use its entity as a vertex for
      --  the returned value. We pull the proof dependencies from its type.
      --  Type invariants from the enclosing unit are pulled only when the
      --  entity is a boundary subprogram.
      if Ekind (FA.Spec_Entity) = E_Function then
         Create_Initial_And_Final_Vertices (FA.Spec_Entity, FA);
         Process_Type_Contracts
           (Etype (FA.Spec_Entity),
            FA.B_Scope,
            Is_Globally_Visible (FA.Spec_Entity),
            FA.Proof_Dependencies);
      end if;

      --  If you're now wondering where we deal with locally declared objects
      --  then we deal with them as they are encountered. See
      --  Do_Object_Declaration for enlightenment.
      --
      --  Here we only deal with abstract states whose constituents will not be
      --  encountered, because they are hidden behind a SPARK_Mode => Off.

      if FA.Kind = Kind_Package
        and then Has_Non_Null_Abstract_State (FA.Spec_Entity)
        and then (not Private_Spec_In_SPARK (FA.Spec_Entity)
                  or else not Entity_Body_In_SPARK (FA.Spec_Entity))
      then
         for State of Iter (Abstract_States (FA.Spec_Entity)) loop
            Create_Initial_And_Final_Vertices (E => State, FA => FA);

            --  As with Do_Object_Declaration, mark the state as export when
            --  it is present as a LHS of an Initializes contract.

            if Present (Find_In_Initializes (State)) then
               declare
                  Final_Out_Id : constant Flow_Id :=
                    Direct_Mapping_Id (State, Final_Value);

                  Final_V_Id : constant Flow_Graphs.Vertex_Id :=
                    FA.CFG.Get_Vertex (Final_Out_Id);

                  Final_Atr : V_Attributes renames FA.Atr (Final_V_Id);
               begin
                  Final_Atr.Is_Export := True;
               end;
            end if;
         end loop;
      end if;

      --  For packages whose analysis stops at the SPARK_Mode => Off, we trust
      --  the explicit Initializes. This only matters for packages with bodies,
      --  because if without a body, there will be no abstract state; without
      --  abstract state the Initializes contract can only reference objects
      --  declared in visible part of the spec; and since there is no body,
      --  those objects can be only initialized at their declarations anyway.

      if FA.Kind = Kind_Package
        and then Present (Get_Pragma (FA.Spec_Entity, Pragma_Initializes))
        and then Present (Body_Entity (FA.Spec_Entity))
        and then (not Private_Spec_In_SPARK (FA.Spec_Entity)
                  or else not Entity_Body_In_SPARK (FA.Spec_Entity)
                  or else not Body_Statements_In_SPARK (FA.Spec_Entity))
      then
         declare
            DM : constant Dependency_Maps.Map :=
              Parse_Initializes (FA.Spec_Entity, FA.B_Scope);

            Curr : Flow_Graphs.Vertex_Id;
            Prev : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;

         begin
            for Clause in DM.Iterate loop
               declare
                  The_Out : Flow_Id renames Dependency_Maps.Key (Clause);
                  The_Ins : Flow_Id_Sets.Set renames DM (Clause);

                  Out_Id : constant Entity_Id :=
                    (if Present (The_Out)
                     then Get_Direct_Mapping_Id (The_Out)
                     else Types.Empty);

                  A : V_Attributes;

                  Split_Out : constant Flow_Id_Sets.Set :=
                    (if Present (The_Out)
                     then Flatten_Variable (The_Out, FA.B_Scope)
                     else Flow_Id_Sets.Empty_Set);

                  Split_Ins : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
               begin
                  --  The extra vertex is only needed for objects and states
                  --  that would be otherwise uninitialized.

                  if Present (Out_Id)
                    and then (Ekind (Out_Id) = E_Constant
                              or else (Ekind (Out_Id) = E_Variable
                                       and then (Has_Initial_Value (Out_Id)
                                                 or else Is_Default_Initialized
                                                           (The_Out))))
                  then
                     goto Next_Clause;
                  end if;

                  --  We will get a relation from an initializes like X => Y.
                  --  But X and Y may be records, and so we need to split up
                  --  both the state and the list of inputs.
                  for The_In of The_Ins loop
                     Split_Ins.Union (Flatten_Variable (The_In, FA.B_Scope));
                  end loop;

                  A :=
                    Make_Basic_Attributes
                      (Var_Def    => Split_Out,
                       Var_Ex_Use => Split_Ins,
                       Vertex_Ctx => No_Vertex_Context);

                  Add_Vertex (FA, A, Curr);
                  FA.Atr (Curr).Is_Package_Initialization := True;

                  if Prev = Flow_Graphs.Null_Vertex then
                     Init_Block := Trivial_Connection (Curr);
                  else
                     Linkup (FA, From => Prev, To => Curr);
                     Init_Block.Standard_Exits := Vertex_Sets.To_Set (Curr);
                  end if;

                  Prev := Curr;
                  <<Next_Clause>>
               end;
            end loop;

            if Prev = Flow_Graphs.Null_Vertex then
               --  We had a null sequence so we need to produce a null node
               Add_Vertex (FA, Null_Node_Attributes, Curr);
               Init_Block := Trivial_Connection (Curr);
            end if;
         end;
      else
         declare
            V : Flow_Graphs.Vertex_Id;
         begin
            --  We had a null sequence so we need to produce a null node
            Add_Vertex (FA, Null_Node_Attributes, V);
            Init_Block := Trivial_Connection (V);
         end;
      end if;

      --  Produce flowgraph for the precondition and postcondition, if any
      case FA.Kind is
         when Kind_Subprogram =>
            --  Flowgraph for preconditions and left hand sides of contract
            --  cases.
            declare
               NL : Union_Lists.List;

            begin
               for Precondition of
                 Get_Precondition_Expressions (FA.Spec_Entity)
               loop
                  Do_Contract_Expression
                    (Precondition, FA, Connection_Map, The_Context);
                  NL.Append (Union_Id (Precondition));
               end loop;
               Join
                 (FA    => FA,
                  CM    => Connection_Map,
                  Nodes => NL,
                  Block => Precon_Block);
            end;

            --  Flowgraph for postconditions and right hand sides of contract
            --  cases.
            declare
               NL : Union_Lists.List;
            begin
               for Refined in Boolean loop
                  for Postcondition of
                    Get_Postcondition_Expressions (FA.Spec_Entity, Refined)
                  loop
                     Do_Contract_Expression
                       (Postcondition, FA, Connection_Map, The_Context);
                     NL.Append (Union_Id (Postcondition));
                  end loop;
               end loop;
               Join
                 (FA    => FA,
                  CM    => Connection_Map,
                  Nodes => NL,
                  Block => Postcon_Block);
            end;

            --  Flowgraph for Exceptional_Cases. We pretend that clauses of the
            --  Exceptional_Cases are executed sequentially, because this is a
            --  good enough approximation. In general, we can't precisely tell
            --  which clause will be executed anyway, e.g.:
            --
            --     procedure P
            --       with Exceptional_Cases =>
            --              (Constraint_Error => ...,
            --              (Program_Error    => ...)
            --     is
            --        ...
            --     exception
            --        when others =>
            --           raise;
            --     end P;

            declare
               Prag  : constant Node_Id :=
                 Get_Pragma (FA.Spec_Entity, Pragma_Exceptional_Cases);
               Aggr  : Node_Id;
               Assoc : Node_Id;
               Expr  : Node_Id;
               NL    : Union_Lists.List;
            begin
               if Present (Prag) then
                  Aggr :=
                    Get_Pragma_Arg
                      (First (Pragma_Argument_Associations (Prag)));

                  Assoc := First (Component_Associations (Aggr));
                  while Present (Assoc) loop
                     Expr := Expression (Assoc);
                     Do_Contract_Expression
                       (Expr, FA, Connection_Map, The_Context);
                     NL.Append (Union_Id (Expr));
                     Next (Assoc);
                  end loop;
               end if;

               Join
                 (FA    => FA,
                  CM    => Connection_Map,
                  Nodes => NL,
                  Block => Excep_Cases_Block);

               --  When an unhandled exception ocurrs, the values of actual
               --  parameters passed by-reference will be transferred to the
               --  caller; for other parameters it doesn't matter what values
               --  they are assigned by the callee. In fact, we DON'T WANT
               --  these values to be represented in the Depends contract
               --  (which we want to describe the dependencies for a normal
               --  termination).
               --
               --  We can handle this with the following choices:
               --  1) leave them unassigned, but this will cause silly checks
               --     insisting on user to assign them according to the Depends
               --     contract;
               --  2) assign them according to the Depends contract, but this
               --     will suppress messages about variables from the RHS of
               --     the Depends clauses that otherwise would appear as
               --     unused;
               --  3) assign them with a null dependency.
               --
               --  The last choice is not strictly right, but gives us exactly
               --  the behaviour that we want. In particular, any explicit
               --  assignments just before the raise statements will become
               --  flagged as unused.

               if Present (Prag) then
                  declare
                     Formal  : Entity_Id;
                     Var_Def : Flow_Id_Sets.Set;
                     Scrub   : Flow_Graphs.Vertex_Id;

                  begin
                     Formal := First_Formal (FA.Spec_Entity);
                     while Present (Formal) loop
                        if Ekind (Formal) = E_In_Parameter
                          and then not Is_Writable_Parameter (Formal)
                        then
                           null;
                        elsif Is_Aliased (Formal)
                          or else Is_By_Reference_Type (Etype (Formal))
                        then
                           null;
                        else
                           Var_Def.Union
                             (Flatten_Variable (Formal, FA.B_Scope));
                        end if;
                        Next_Formal (Formal);
                     end loop;

                     --  Handle 'Result just like a by-copy formal parameter
                     --  of mode OUT, so that function (with side effects) is
                     --  represented similarly to a procedure with parameter
                     --  of mode OUT.

                     if Is_Function_With_Side_Effects (FA.Spec_Entity) then
                        Var_Def.Union
                          (Flatten_Variable (FA.Spec_Entity, FA.B_Scope));
                     end if;

                     Add_Vertex
                       (FA,
                        Make_Basic_Attributes
                          (Var_Def    => Var_Def,
                           Vertex_Ctx => The_Context.Vertex_Ctx,
                           Print_Hint => Pretty_Print_Param_Scrub),
                        Scrub);
                     FA.Atr (Scrub).Is_Program_Node := False;

                     Linkup
                       (FA,
                        Froms => Excep_Cases_Block.Standard_Exits,
                        To    => Scrub);

                     Excep_Cases_Block.Standard_Exits :=
                       Vertex_Sets.To_Set (Scrub);
                  end;
               end if;
            end;

         when Kind_Task =>
            --  No pre or post here
            null;

         when Kind_Package =>
            --  Flowgraph for initial_condition aspect
            declare
               NL : Union_Lists.List := Union_Lists.Empty_List;

            begin
               for Postcondition of
                 Get_Postcondition_Expressions
                   (FA.Spec_Entity, Refined => False)
               loop
                  Do_Contract_Expression
                    (Postcondition, FA, Connection_Map, The_Context);
                  NL.Append (Union_Id (Postcondition));
               end loop;
               Join
                 (FA    => FA,
                  CM    => Connection_Map,
                  Nodes => NL,
                  Block => Postcon_Block);
            end;

      end case;

      --  Produce flowgraphs for the body and link to start, helper end and end
      --  vertex.
      case FA.Kind is
         when Kind_Subprogram =>
            Do_Subprogram_Or_Block (Body_N, FA, Connection_Map, The_Context);

            --  Connect up all the dots...
            Linkup (FA, FA.Start_Vertex, Precon_Block.Standard_Entry);
            Linkup
              (FA,
               Precon_Block.Standard_Exits,
               Connection_Map (Union_Id (Body_N)).Standard_Entry);
            Linkup
              (FA,
               Connection_Map (Union_Id (Body_N)).Standard_Exits,
               FA.Helper_End_Vertex);
            Linkup (FA, FA.Helper_End_Vertex, Postcon_Block.Standard_Entry);
            Linkup
              (FA,
               FA.Exceptional_End_Vertex,
               Excep_Cases_Block.Standard_Entry);
            Linkup (FA, Excep_Cases_Block.Standard_Exits, FA.End_Vertex);
            Linkup (FA, Postcon_Block.Standard_Exits, FA.End_Vertex);

         when Kind_Task =>
            Do_Subprogram_Or_Block (Body_N, FA, Connection_Map, The_Context);

            Linkup
              (FA,
               FA.Start_Vertex,
               Connection_Map (Union_Id (Body_N)).Standard_Entry);
            Linkup
              (FA,
               Connection_Map (Union_Id (Body_N)).Standard_Exits,
               FA.Helper_End_Vertex);
            Linkup (FA, FA.Helper_End_Vertex, FA.End_Vertex);

         when Kind_Package =>
            declare
               Nodes : Union_Lists.List := Union_Lists.Empty_List;
               Block : Graph_Connections;
               --  List of nodes that represent the order in which a package is
               --  elaborated; it is then abstracted into a single block.

               Visible_Decls : constant List_Id :=
                 Visible_Declarations (Spec_N);

               Private_Decls : constant List_Id :=
                 Private_Declarations (Spec_N);

            begin
               if Present (Visible_Decls) then
                  Process_Statement_List
                    (Visible_Decls, FA, Connection_Map, The_Context);

                  Nodes.Append (Union_Id (Visible_Decls));
               end if;

               if Private_Spec_In_SPARK (FA.Spec_Entity) then
                  if Present (Private_Decls) then

                     Process_Statement_List
                       (Private_Decls, FA, Connection_Map, The_Context);
                     Nodes.Append (Union_Id (Private_Decls));
                  end if;

                  if Entity_Body_In_SPARK (FA.Spec_Entity) then
                     Do_Subprogram_Or_Block
                       (Body_N, FA, Connection_Map, The_Context);
                     Nodes.Append (Union_Id (Body_N));
                  end if;
               end if;

               Join
                 (FA    => FA,
                  CM    => Connection_Map,
                  Nodes => Nodes,
                  Block => Block);

               Linkup (FA, FA.Start_Vertex, Block.Standard_Entry);

               Linkup (FA, Block.Standard_Exits, FA.Helper_End_Vertex);

               Linkup (FA, FA.Helper_End_Vertex, Init_Block.Standard_Entry);

               Linkup
                 (FA, Init_Block.Standard_Exits, Postcon_Block.Standard_Entry);

               Linkup (FA, Postcon_Block.Standard_Exits, FA.End_Vertex);

            end;
      end case;

      --  Label all vertices that are part of exceptional execution paths
      Mark_Exceptional_Paths (FA);

      Prune_Dead_Paths (FA);

      --  Simplify graph by removing all null vertices
      Simplify_CFG (FA);

      --  In GG mode, we now assemble globals and retroactively make some
      --  initial and final vertices, which is the only reason for this code
      --  to be here.
      if FA.Generating_Globals then
         --  Assemble the set of directly called subprograms
         for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
            declare
               Atr : V_Attributes renames FA.Atr (V);
            begin
               --  Ignore vertices from nested packages. Theirs subprogram
               --  calls will become direct calls of those nested packages.

               if not Atr.In_Nested_Package then
                  FA.Direct_Calls.Union
                    (To_Subprograms (Atr.Subprogram_Calls));

                  --  Calls to entries and to predefined potentially blocking
                  --  subprograms make this entity potentially blocking.
                  --  We do this here, because otherwise we would
                  --  have to do it in both Do_Call_Statement and
                  --  Pick_Generated_Info.

                  if FA.Has_Only_Nonblocking_Statements then
                     for SC of Atr.Subprogram_Calls loop
                        if Is_Entry (SC.E)
                          or else (Ekind (SC.E) in E_Function | E_Procedure
                                   and then Is_Predefined_Potentially_Blocking
                                              (SC.E))
                          or else (Nkind (SC.N) in N_Subprogram_Call
                                   and then Flow_Classwide.Is_Dispatching_Call
                                              (SC.N))
                        then
                           FA.Has_Only_Nonblocking_Statements := False;
                           exit;
                        end if;
                     end loop;
                  end if;

                  --  Same for problematic calls that make the subprogram
                  --  potentially nonterminating:
                  --  * dispatching calls,
                  --  * calls via access-to-subprogram,
                  --  * procedures from the standard library with No_Return.

                  if FA.Has_Only_Terminating_Constructs then
                     for SC of Atr.Subprogram_Calls loop
                        if (Nkind (SC.N) in N_Subprogram_Call
                            and then Flow_Classwide.Is_Dispatching_Call (SC.N))
                          or else Ekind (SC.E) = E_Subprogram_Type
                          or else (Is_Ignored_Internal (SC.E)
                                   and then Is_Subprogram (SC.E)
                                   and then No_Return (SC.E))
                        then
                           FA.Has_Only_Terminating_Constructs := False;
                           exit;
                        end if;
                     end loop;
                  end if;

                  --  Indirect calls to equality can make the subprogram
                  --  nonterminating. We flag calls to dispatching equalities
                  --  and add called primitive equalities in the callees set.

                  for N of Atr.Indirect_Calls loop
                     declare
                        Typ : constant Entity_Id :=
                          (if Nkind (N) = N_Function_Call
                           then Etype (First_Actual (N))
                           else Etype (Left_Opnd (N)));
                     begin
                        if Calls_Dispatching_Equality (N) then
                           FA.Has_Only_Terminating_Constructs := False;
                           Process_Indirect_Dispatching_Equality
                             (Typ, FA.Proof_Dependencies);
                        else
                           FA.Direct_Calls.Union
                             (Called_Primitive_Equalities
                                (Typ, Nkind (N) in N_Op));
                        end if;
                     end;
                  end loop;
               end if;
            end;
         end loop;

         --  Direct calls might only contain callable entities and nested
         --  packages.
         pragma
           Assert
             (for all E of FA.Direct_Calls =>
                Ekind (E)
                in Entry_Kind
                 | E_Function
                 | E_Package
                 | E_Procedure
                 | E_Subprogram_Type);

         declare
            --  ??? this block should operate just on Entity_Ids
            Known_Vars : constant Flow_Id_Sets.Set :=
              To_Entire_Variables (FA.All_Vars);
         begin
            for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
               declare
                  Atr  : V_Attributes renames FA.Atr (V);
                  Vars : constant Flow_Id_Sets.Set :=
                    To_Entire_Variables
                      (Atr.Variables_Used or Atr.Variables_Defined);
               begin
                  for Var of Vars loop
                     if not Known_Vars.Contains (Var) then
                        FA.GG.Globals.Include (Get_Direct_Mapping_Id (Var));
                     end if;
                  end loop;
               end;
            end loop;
         end;

         for E of FA.GG.Globals loop
            Create_Initial_And_Final_Vertices
              (Direct_Mapping_Id (E),
               (if Ekind (E) in E_In_Parameter | E_Constant
                then Mode_In
                else Mode_In_Out),
               FA);

            --  Collect accesses to not-synchronized library-level entities

            if Is_Library_Level_Entity (E) and then not Is_Synchronized (E)
            then
               FA.Tasking (Unsynch_Accesses).Insert (E);
            end if;
         end loop;

         --  For callees that might have outputs, i.e. procedures and entries,
         --  and specifically those whose Global/Depends contract have not been
         --  "inlined" when building the CFG, we need extra vertices to decide
         --  which of them are called definitively (so that we know that their
         --  outputs will be definitely written) as opposed to conditional (so
         --  that we model such outputs as read-writes).

         for E of FA.Direct_Calls loop
            if (Ekind (E) in E_Procedure | E_Entry
                or else Is_Function_With_Side_Effects (E))
              and then (not Has_User_Supplied_Globals (E)
                        or else Rely_On_Generated_Global (E, FA.B_Scope))
            then
               declare
                  F_Initial : constant Flow_Id :=
                    Direct_Mapping_Id (E, Initial_Value);
                  F_Final   : constant Flow_Id :=
                    Direct_Mapping_Id (E, Final_Value);

                  V : Flow_Graphs.Vertex_Id;

               begin
                  --  Setup the n'initial vertex
                  Add_Vertex
                    (FA,
                     F_Initial,
                     Make_Variable_Attributes
                       (F_Ent => F_Initial, Mode => Mode_In_Out, E_Loc => E),
                     V);
                  Linkup (FA, V, FA.Start_Vertex);

                  --  Setup the n'final vertex
                  Add_Vertex
                    (FA,
                     F_Final,
                     Make_Variable_Attributes
                       (F_Ent => F_Final, Mode => Mode_In_Out, E_Loc => E),
                     V);
                  Linkup (FA, FA.End_Vertex, V);
               end;
            end if;
         end loop;
      end if;

      --  Store the original CFG, before pruning, which is only needed to
      --  compute CDG.

      FA.Full_CFG := FA.CFG;
      FA.Full_Atr := FA.Atr;

      --  Remove exceptional paths, because they would crash the post-dominance
      --  frontier calculation.
      Prune_Exceptional_Paths (FA);

      --  Make sure we will be able to produce the post-dominance frontier
      --  if we have dead code remaining.
      Separate_Dead_Paths (FA);

      --  Simplify graph by removing all null vertices
      Simplify_CFG (FA);

      --  Finally, make sure that all extra checks for folded functions have
      --  been processed and other context information has been dropped.
      pragma Assert (The_Context = No_Context);
   end Create;

end Flow.Control_Flow_Graph;
