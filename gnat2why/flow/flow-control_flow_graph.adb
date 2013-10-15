------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              F L O W . C O N T R O L _ F L O W _ G R A P H               --
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

with Ada.Containers.Doubly_Linked_Lists;

with Errout;
with Nlists;                          use Nlists;
with Sem_Eval;                        use Sem_Eval;
with Sem_Util;                        use Sem_Util;
with Sinfo;                           use Sinfo;
with Snames;                          use Snames;

with Treepr;                          use Treepr;

with Flow.Debug;                      use Flow.Debug;
pragma Unreferenced (Flow.Debug);

with Flow.Antialiasing;               use Flow.Antialiasing;
with Flow.Control_Flow_Graph.Utility; use Flow.Control_Flow_Graph.Utility;
with Flow.Utility;                    use Flow.Utility;
with Flow_Error_Messages;             use Flow_Error_Messages;

with Why;

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
   --  Debug
   ------------------------------------------------------------

   Debug_Print_Assignment_Def_Use_Sets_And_Tree : constant Boolean := False;
   --  Enable this to debug print the node and its def-use effect

   ------------------------------------------------------------
   --  Local types
   ------------------------------------------------------------

   ----------------------
   --  Connection_Maps --
   ----------------------

   type Graph_Connections is record
      Standard_Entry : Flow_Graphs.Vertex_Id;
      Standard_Exits : Vertex_Sets.Set;
   end record;

   No_Connections : constant Graph_Connections :=
     Graph_Connections'(Standard_Entry => Flow_Graphs.Null_Vertex,
                        Standard_Exits => Vertex_Sets.Empty_Set);

   function Union_Hash (X : Union_Id) return Ada.Containers.Hash_Type
   is (Ada.Containers.Hash_Type (abs (X)));

   package Connection_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Union_Id,
      Element_Type    => Graph_Connections,
      Hash            => Union_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   --------------
   --  Context --
   --------------

   type Context is record
      Current_Loops    : Node_Sets.Set;
      --  The set of loops currently processed. The innermost loop
      --  currently processed is Active_Loop.

      Active_Loop      : Entity_Id;
      --  The currently processed loop. This is always a member of
      --  Current_Loops, unless no loop is currently processed.

      Entry_References : Node_Graphs.Map;
      --  A map from loops -> 'loop_entry references.
   end record;

   No_Context : constant Context :=
     Context'(Current_Loops    => Node_Sets.Empty_Set,
              Active_Loop      => Empty,
              Entry_References => Node_Graphs.Empty_Map);

   ------------------------------------------------------------
   --  Local declarations
   ------------------------------------------------------------

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
     (CFG   : in out Flow_Graphs.T;
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
   --  Deal with declarations (with an optional initialisation). We
   --  either generate a null vertex which is then stripped from the
   --  graph or a simple defining vertex.

   procedure Do_Pragma
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Pragma;
   --  Deals with pragmas. We only check for uninitialised variables. We
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
   --  This is the top level procedure which deals with a subprogam,
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
     (Callsite          : Node_Id;
      Refined_View      : Boolean;
      In_List           : in out Vertex_Vectors.Vector;
      Out_List          : in out Vertex_Vectors.Vector;
      FA                : in out Flow_Analysis_Graphs;
      CM                : in out Connection_Maps.Map;
      Ctx               : in out Context);
   --  This procedures creates the in and out vertices for a
   --  subprogram's globals. They are not connected to anything,
   --  instead the vertices are added to the given in_list and
   --  out_list.

   procedure Process_Parameter_Associations
     (L                 : List_Id;
      Called_Subprogram : Entity_Id;
      In_List           : in out Vertex_Vectors.Vector;
      Out_List          : in out Vertex_Vectors.Vector;
      FA                : in out Flow_Analysis_Graphs;
      CM                : in out Connection_Maps.Map;
      Ctx               : in out Context);
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
      Ctx : in out Context);
   --  Process an arbitrary statement (this is basically a big case
   --  block which calls the various Do_XYZ procedures).

   procedure Simplify
     (G : in out Flow_Graphs.T'Class);
   --  Remove all null vertices from the graph.

   function Pragma_Relevant_To_Flow (N : Node_Id) return Boolean
     with Pre => Nkind (N) = N_Pragma;
   --  Check if flow analysis cares about this particular pragma.

   ------------------------------------------------------------
   --  Local procedures and functions
   ------------------------------------------------------------

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
     (CFG   : in out Flow_Graphs.T;
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
            Linkup (CFG,
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
         CFG.Add_Vertex (Null_Node_Attributes,
                         V);
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
               when Direct_Mapping =>
                  null;
               when Record_Field =>
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
               when Magic_String =>
                  null;
            end case;

         when Initial_Grouping | Final_Grouping =>
            case F.Kind is
               when Null_Value =>
                  raise Program_Error;
               when Direct_Mapping | Record_Field =>
                  --  Only proceed if we don't have this vertex yet.
                  if FA.CFG.Get_Vertex (F) = Flow_Graphs.Null_Vertex then
                     --  Create vertex.
                     FA.CFG.Add_Vertex
                       (F,
                        Make_Record_Tree_Attributes (Leaf_Atr));

                     if F.Kind = Record_Field then
                        Create_Record_Tree (Parent_Record (F), Leaf_Atr, FA);
                        Linkup (FA.CFG,
                                FA.CFG.Get_Vertex (Parent_Record (F)),
                                FA.CFG.Get_Vertex (F));
                     end if;
                  end if;
               when Magic_String =>
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
      V : Flow_Graphs.Vertex_Id;
      A : V_Attributes;
      M : Param_Mode;
   begin
      if Ekind (E) = E_Constant then
         --  We ignore constants (for now).
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

      for F of Flatten_Variable (E) loop
         --  Setup the n'initial vertex. Note that initialisation for
         --  variables is detected (and set) when building the flow graph
         --  for declarative parts.
         A := Make_Variable_Attributes (F_Ent => Change_Variant
                                          (F, Initial_Value),
                                        Mode  => M,
                                        E_Loc => E);
         FA.CFG.Add_Vertex
           (Change_Variant (F, Initial_Value),
            A,
            V);
         Linkup (FA.CFG, V, FA.Start_Vertex);

         Create_Record_Tree (Change_Variant (F, Initial_Value),
                             A,
                             FA);

         --  Setup the n'final vertex.
         FA.CFG.Add_Vertex
           (Change_Variant (F, Final_Value),
            Make_Variable_Attributes (F_Ent => Change_Variant
                                        (F, Final_Value),
                                      Mode  => M,
                                      E_Loc => E),
            V);
         Linkup (FA.CFG, FA.End_Vertex, V);

         FA.All_Vars.Include (F);
      end loop;
   end Create_Initial_And_Final_Vertices;

   procedure Create_Initial_And_Final_Vertices
     (F             : Flow_Id;
      Mode          : Param_Mode;
      Uninitialized : Boolean;
      FA            : in out Flow_Analysis_Graphs)
   is
      V : Flow_Graphs.Vertex_Id;
      A : V_Attributes;
   begin
      for F_Part of Flatten_Variable (F) loop
         --  Setup the n'initial vertex. Initialisation is deduced from
         --  the mode.
         A := Make_Global_Variable_Attributes
           (F      => Change_Variant (F_Part, Initial_Value),
            Mode   => Mode,
            Uninit => Uninitialized);
         FA.CFG.Add_Vertex
           (Change_Variant (F_Part, Initial_Value),
            A,
            V);
         Linkup (FA.CFG, V, FA.Start_Vertex);

         Create_Record_Tree (Change_Variant (F_Part, Initial_Value),
                             A,
                             FA);

         --  Setup the n'final vertex.
         FA.CFG.Add_Vertex
           (Change_Variant (F_Part, Final_Value),
            Make_Global_Variable_Attributes
              (F    => Change_Variant (F_Part, Final_Value),
               Mode => Mode),
            V);
         Linkup (FA.CFG, FA.End_Vertex, V);

         FA.All_Vars.Include (F_Part);
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
      V : Flow_Graphs.Vertex_Id;

      V_Used_RHS  : Flow_Id_Sets.Set;
      --  Things used because they appear on the RHS

      V_Used_LHS  : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      --  Things used because they appear on the LHS (in A (J), J
      --  would be used).

      V_Def_LHS   : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      --  Things defined because they appear on the LHS (in A (J), A
      --  would be used).
   begin
      --  Work out which variables we use and define.
      V_Used_RHS := Get_Variable_Set (FA.Scope, Expression (N));

      Untangle_Assignment_Target (Scope        => FA.Scope,
                                  N            => Name (N),
                                  Vars_Used    => V_Used_LHS,
                                  Vars_Defined => V_Def_LHS);

      if Debug_Print_Assignment_Def_Use_Sets_And_Tree then
         Print_Node_Subtree (N);
         Print_Node_Set (V_Def_LHS);
         Print_Node_Set (V_Used_LHS or V_Used_RHS);
      end if;

      --  We have a vertex
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (N),
         Make_Basic_Attributes (Var_Def => V_Def_LHS,
                                Var_Use => V_Used_RHS or
                                  V_Used_LHS,
                                Loops   => Ctx.Current_Loops,
                                E_Loc   => N),
         V);

      --  Control goes in V and of V
      CM.Include (Union_Id (N),
                  Graph_Connections'
                    (Standard_Entry => V,
                     Standard_Exits => Vertex_Sets.To_Set (V)));
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
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (N),
         Make_Basic_Attributes (Var_Use => Get_Variable_Set
                                  (FA.Scope, Expression (N)),
                                Loops   => Ctx.Current_Loops,
                                E_Loc   => N),
         V);
      CM.Include (Union_Id (N), No_Connections);
      CM (Union_Id (N)).Standard_Entry := V;

      Alternative := First (Alternatives (N));

      while Present (Alternative) loop
         --  We introduce a vertex V_Alter for each
         --  Case_Statement_Alternative and we link that to V.
         FA.CFG.Add_Vertex
           (Direct_Mapping_Id (Alternative),
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
         FA.CFG.Add_Vertex (Direct_Mapping_Id (N),
                            Null_Node_Attributes,
                            V);
         CM.Include (Union_Id (N),
                     Graph_Connections'
                       (Standard_Entry => V,
                        Standard_Exits => Vertex_Sets.Empty_Set));

         CM (Union_Id (L)).Standard_Exits.Include (V);

      else
         FA.CFG.Add_Vertex
           (Direct_Mapping_Id (N),
            Make_Basic_Attributes (Var_Use => Get_Variable_Set (FA.Scope,
                                                                Condition (N)),
                                   Loops   => Ctx.Current_Loops,
                                   E_Loc   => N),
            V);
         CM.Include (Union_Id (N),
                     Graph_Connections'
                       (Standard_Entry => V,
                        Standard_Exits => Vertex_Sets.To_Set (V)));

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
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (N),
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
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (Ret_Entity),
         Make_Extended_Return_Attributes
              (Var_Def         => Flatten_Variable (FA.Analyzed_Entity),
               Var_Use         => Get_Variable_Set (FA.Scope, Ret_Object),
               Object_Returned => Ret_Object,
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

      --  We link the implicit return statement to the end_vertex
      Linkup (FA.CFG, V, FA.End_Vertex);

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
      --  !!! Workaround for stdlib bug
      CM.Include (Union_Id (N), CM.Element (Union_Id (Stmts)));
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
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (N),
         Make_Basic_Attributes (Var_Use => Get_Variable_Set (FA.Scope,
                                                             Condition (N)),
                                Loops   => Ctx.Current_Loops,
                                E_Loc   => N),
         V);
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
               FA.CFG.Add_Vertex
                 (Direct_Mapping_Id (Elsif_Statement),
                  Make_Basic_Attributes (Var_Use => Get_Variable_Set
                                           (FA.Scope,
                                            Condition (Elsif_Statement)),
                                         Loops   => Ctx.Current_Loops,
                                         E_Loc   => Elsif_Statement),
                  V);
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

      procedure Do_For_Loop;
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
      --  also flagged as Is_Initialised and Is_Loop_Parameter so that
      --  it can be suitably ignored by subsequent analysis).
      --
      --  We distinguish this case (non-empty range) from the previous
      --  one (unknown range) as subsequent code may rely on any
      --  initializations in the loop body.

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
         FA.CFG.Add_Vertex (Direct_Mapping_Id (N),
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
            FA.CFG.Add_Vertex
              (Direct_Mapping_Id (End_Label (N)),
               Make_Aux_Vertex_Attributes (E_Loc => N),
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

      procedure Do_While_Loop
      is
         V : Flow_Graphs.Vertex_Id;
      begin
         FA.CFG.Add_Vertex
           (Direct_Mapping_Id (N),
            Make_Basic_Attributes (Var_Use => Get_Variable_Set
                                     (FA.Scope,
                                      Condition (Iteration_Scheme (N))),
                                   Loops   => Ctx.Current_Loops,
                                   E_Loc   => N),
            V);

         --  Flow for the while loops goes into the condition and then
         --  out again.
         CM (Union_Id (N)).Standard_Entry := V;
         CM (Union_Id (N)).Standard_Exits.Include (V);

         --  Loop the loop: V -> body -> V
         Linkup (FA.CFG, V, CM (Union_Id (Statements (N))).Standard_Entry);
         Linkup (FA.CFG, CM (Union_Id (Statements (N))).Standard_Exits, V);
      end Do_While_Loop;

      procedure Do_For_Loop
      is
         LPS : constant Node_Id :=
           Loop_Parameter_Specification (Iteration_Scheme (N));

         LP : constant Entity_Id := Defining_Identifier (LPS);

         DSD : constant Node_Id := Discrete_Subtype_Definition (LPS);

         R : Node_Id;
         V : Flow_Graphs.Vertex_Id;
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

         --  We have a new variable here which we have not picked up
         --  in Create, so we should set it up.
         Create_Initial_And_Final_Vertices (LP, False, FA);

         --  Work out which of the three variants (empty, full,
         --  unknown) we have...
         if Is_Null_Range (Low_Bound (R), High_Bound (R)) then
            --  We have an empty range. We should complain!
            FA.CFG.Add_Vertex
              (Direct_Mapping_Id (N),
               Make_Basic_Attributes
                 (Var_Def => Flatten_Variable (LP),
                  Loops   => Ctx.Current_Loops,
                  E_Loc   => N),
               V);

            --  Flow goes into and out of the loop. Note that we do
            --  NOT hook up the loop body.
            CM (Union_Id (N)).Standard_Entry := V;
            CM (Union_Id (N)).Standard_Exits.Include (V);

         elsif Not_Null_Range (Low_Bound (R), High_Bound (R)) then
            --  We need to make sure the loop is executed at least once.

            FA.CFG.Add_Vertex
              (Direct_Mapping_Id (N),
               Make_Basic_Attributes
                 (Var_Def => Flatten_Variable (LP),
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

         else
            --  We don't know if the loop will be executed or not.
            FA.CFG.Add_Vertex
              (Direct_Mapping_Id (N),
               Make_Basic_Attributes
                 (Var_Def => Flatten_Variable (LP),
                  Var_Use => Get_Variable_Set (FA.Scope, DSD),
                  Loops   => Ctx.Current_Loops,
                  E_Loc   => N),
               V);

            --  Flow for the conditional for loop is like a while
            --  loop.
            CM (Union_Id (N)).Standard_Entry := V;
            CM (Union_Id (N)).Standard_Exits.Include (V);

            --  Loop the loop: V -> body -> V
            Linkup (FA.CFG, V, CM (Union_Id (Statements (N))).Standard_Entry);
            Linkup (FA.CFG, CM (Union_Id (Statements (N))).Standard_Exits, V);
         end if;
      end Do_For_Loop;

      Previous_Loop  : constant Entity_Id := Ctx.Active_Loop;

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
      FA.Loops.Insert (Entity (Identifier (N)));
      Ctx.Current_Loops.Insert (Entity (Identifier (N)));
      Ctx.Active_Loop := Entity (Identifier (N));
      Ctx.Entry_References.Include (Ctx.Active_Loop, Node_Sets.Empty_Set);

      Process_Statement_List (Statements (N), FA, CM, Ctx);

      Ctx.Current_Loops.Delete (Entity (Identifier (N)));
      Ctx.Active_Loop := Previous_Loop;

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

            Do_For_Loop;
         end if;
      end if;

      --  Now we need to glue the 'loop_entry checks to the front of
      --  the loop.
      declare
         Augmented_Loop : Union_Lists.List := Union_Lists.Empty_List;
         V              : Flow_Graphs.Vertex_Id;
         Block          : Graph_Connections;
      begin
         --  We stick all loop entry references on a list of nodes.
         for Reference of Ctx.Entry_References (Entity (Identifier (N))) loop
            FA.CFG.Add_Vertex
              (Direct_Mapping_Id (Reference),
               Make_Sink_Vertex_Attributes
                 (Var_Use       => Get_Variable_Set (FA.Scope,
                                                     Prefix (Reference)),
                  Is_Loop_Entry => True),
               V);

            CM.Include
              (Union_Id (Reference),
               Graph_Connections'(Standard_Entry => V,
                                  Standard_Exits => Vertex_Sets.To_Set (V)));

            Augmented_Loop.Append (Union_Id (Reference));
         end loop;

         --  Then we stick the actual loop at the end.
         Augmented_Loop.Append (Union_Id (N));

         --  And connect up the dots, and finally replacing the
         --  connection map we have for N with the new augmented one.
         Join (CFG   => FA.CFG,
               CM    => CM,
               Nodes => Augmented_Loop,
               Block => Block);
         CM (Union_Id (N)) := Block;
      end;

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
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (N),
         Make_Aux_Vertex_Attributes (E_Loc => N),
         V);
      CM.Include (Union_Id (N), No_Connections);
      CM (Union_Id (N)).Standard_Entry := V;
      CM (Union_Id (N)).Standard_Exits.Insert (V);
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
      V     : Flow_Graphs.Vertex_Id;
      Inits : Vertex_Vectors.Vector := Vertex_Vectors.Empty_Vector;
   begin
      --  First, we need a 'initial and 'final vertex for this object.
      Create_Initial_And_Final_Vertices (Defining_Identifier (N), False, FA);

      if not Present (Expression (N)) then
         --  No initializing expression, so we fall back to the
         --  default initialization (if any).
         for F of Flatten_Variable (Defining_Identifier (N)) loop
            declare
               DI : constant Node_Id := Get_Default_Initialization (F);
            begin
               if Present (DI) then
                  FA.CFG.Add_Vertex
                    (Make_Default_Initialization_Attributes
                       (Scope => FA.Scope,
                        F     => F,
                        Loops => Ctx.Current_Loops,
                        E_Loc => DI),
                     V);
                  Inits.Append (V);
               end if;
            end;
         end loop;

         if Inits.Length = 0 then
            --  We did not have anything with a default initial value,
            --  so we just create a null vertex here.
            FA.CFG.Add_Vertex (Direct_Mapping_Id (N),
                               Null_Node_Attributes,
                               V);
            Inits.Append (V);
         end if;

      elsif Constant_Present (N) then
         --  We have a sink vertex as we have a constant declaration
         --  (so we need to check for uninitialized variables) but
         --  otherwise have no flow.
         FA.CFG.Add_Vertex
           (Direct_Mapping_Id (N),
            Make_Sink_Vertex_Attributes
              (Var_Use => Get_Variable_Set (FA.Scope, Expression (N)),
               E_Loc   => N),
            V);
         Inits.Append (V);

      else
         --  We have a variable declaration with an initialization.
         FA.CFG.Add_Vertex
           (Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Var_Def => Flatten_Variable (Defining_Identifier (N)),
               Var_Use => Get_Variable_Set (FA.Scope, Expression (N)),
               Loops   => Ctx.Current_Loops,
               E_Loc   => N),
            V);
         Inits.Append (V);
      end if;

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

   end Do_Object_Declaration;

   ---------------
   -- Do_Pragma --
   ---------------

   procedure Do_Pragma
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      function Proc (N : Node_Id) return Traverse_Result;
      --  Adds N to the appropriate entry references of the current
      --  context, if N is a loop_entry reference.

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
         --  If we care, we create a sink vertex to check for
         --  uninitialised variables.
         FA.CFG.Add_Vertex
           (Direct_Mapping_Id (N),
            Make_Sink_Vertex_Attributes
              (Var_Use => Get_Variable_Set (FA.Scope,
                                            Pragma_Argument_Associations (N)),
               E_Loc   => N),
            V);

         case Get_Pragma_Id (N) is

            when Pragma_Unmodified   |
                 Pragma_Unreferenced =>

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
               null;
         end case;

      else
         --  Otherwise we produce a null vertex.
         FA.CFG.Add_Vertex (Null_Node_Attributes,
                            V);
      end if;

      CM.Include (Union_Id (N), No_Connections);
      CM (Union_Id (N)).Standard_Entry := V;
      CM (Union_Id (N)).Standard_Exits := To_Set (V);

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
      --  We just need to check for uninitialised variables.
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (Pre),
         Make_Sink_Vertex_Attributes
           (Var_Use         => Get_Variable_Set (FA.Scope, Pre),
            Is_Precondition => True,
            E_Loc           => Pre),
         V);

      CM.Include (Union_Id (Pre), No_Connections);
      CM (Union_Id (Pre)).Standard_Entry := V;
      CM (Union_Id (Pre)).Standard_Exits := To_Set (V);
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

      V        : Flow_Graphs.Vertex_Id;

      In_List  : Vertex_Vectors.Vector := Vertex_Vectors.Empty_Vector;
      Out_List : Vertex_Vectors.Vector := Vertex_Vectors.Empty_Vector;

      Refined_View : constant Boolean := Should_Use_Refined_View (FA.Scope, N);
   begin
      --  A vertex for the actual call.
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (N),
         Make_Call_Attributes (Callsite     => N,
                               Refined_View => Refined_View,
                               Loops        => Ctx.Current_Loops,
                               E_Loc        => N),
         V);

      --  Deal with the procedures parameters.
      Process_Parameter_Associations (Parameter_Associations (N),
                                      Called_Procedure,
                                      In_List,
                                      Out_List,
                                      FA, CM, Ctx);

      --  Process globals.
      Process_Subprogram_Globals (N,
                                  Refined_View,
                                  In_List, Out_List,
                                  FA, CM, Ctx);

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

            Prev := V;
         end loop;

         CM.Include
           (Union_Id (N),
            Graph_Connections'(Standard_Entry => V,
                               Standard_Exits => Vertex_Sets.To_Set (Prev)));
      end;
   end Do_Procedure_Call_Statement;

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
         FA.CFG.Add_Vertex (Direct_Mapping_Id (N),
                            Make_Aux_Vertex_Attributes (E_Loc => N),
                            V);
      else
         --  We have a function return.
         FA.CFG.Add_Vertex
           (Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Var_Def => Flatten_Variable (FA.Analyzed_Entity),
               Var_Use => Get_Variable_Set (FA.Scope, Expression (N)),
               Loops   => Ctx.Current_Loops,
               E_Loc   => N),
            V);
      end if;

      --  Control flows in, but we do not flow out again.
      CM.Include (Union_Id (N),
                  Graph_Connections'(Standard_Entry => V,
                                     Standard_Exits => Empty_Set));

      --  Instead we link this vertex directly to the end vertex.
      Linkup (FA.CFG, V, FA.End_Vertex);
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
         Do_Handled_Sequence_Of_Statements
           (Handled_Statement_Sequence (N), FA, CM, Ctx);
      end if;

      if Present (Declarations (N)) and
        Present (Handled_Statement_Sequence (N))
      then
         Linkup
           (FA.CFG,
            CM (Union_Id (Declarations (N))).Standard_Exits,
            CM (Union_Id (Handled_Statement_Sequence (N))).Standard_Entry);

         --  !!! Workaround for stdlib bug
         CM.Include
           (Union_Id (N),
            Graph_Connections'
              (Standard_Entry => CM.Element
                 (Union_Id (Declarations (N))).Standard_Entry,
               Standard_Exits => CM.Element
                 (Union_Id (Handled_Statement_Sequence (N))).Standard_Exits));

      elsif Present (Declarations (N)) then
         --  !!! Workaround for stdlib bug
         CM.Include
           (Union_Id (N),
            Graph_Connections'
              (Standard_Entry => CM.Element
                 (Union_Id (Declarations (N))).Standard_Entry,
               Standard_Exits => CM.Element
                 (Union_Id (Declarations (N))).Standard_Exits));

      elsif Present (Handled_Statement_Sequence (N)) then
         --  !!! Workaround for stdlib bug
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
            FA.CFG.Add_Vertex
              (Direct_Mapping_Id (N),
               Make_Aux_Vertex_Attributes (E_Loc => N),
               V);
            CM.Include (Union_Id (N), No_Connections);
            CM (Union_Id (N)).Standard_Entry := V;
            CM (Union_Id (N)).Standard_Exits.Insert (V);
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
      pragma Unreferenced (Ctx);

      V : Flow_Graphs.Vertex_Id;
   begin
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (N),
         Make_Sink_Vertex_Attributes
           (Var_Use => Get_Variable_Set (FA.Scope, N),
            E_Loc   => N),
         V);
      CM.Include (Union_Id (N),
                  Graph_Connections'(Standard_Entry => V,
                                     Standard_Exits => To_Set (V)));
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
      pragma Unreferenced (CM);
      pragma Unreferenced (Ctx);

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
               --  Sanity check: Iterator_Specification is not in
               --  SPARK so it should always be empty.
               pragma Assert (not Present (Iterator_Specification (N)));

               Create_Initial_And_Final_Vertices
                 (Defining_Identifier (Loop_Parameter_Specification (N)),
                  False,
                  FA);

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
     (Callsite          : Node_Id;
      Refined_View      : Boolean;
      In_List           : in out Vertex_Vectors.Vector;
      Out_List          : in out Vertex_Vectors.Vector;
      FA                : in out Flow_Analysis_Graphs;
      CM                : in out Connection_Maps.Map;
      Ctx               : in out Context)
   is
      pragma Unreferenced (CM);

      Reads  : Flow_Id_Sets.Set;
      Writes : Flow_Id_Sets.Set;
      V      : Flow_Graphs.Vertex_Id;
      Atr    : V_Attributes;
   begin
      --  Obtain globals (either from contracts or the computed
      --  stuff).
      Get_Globals (Subprogram   => Entity (Name (Callsite)),
                   Reads        => Reads,
                   Writes       => Writes,
                   Refined_View => Refined_View);

      for R of Reads loop
         FA.CFG.Add_Vertex (Make_Global_Attributes
                              (Call_Vertex        => Callsite,
                               Global             => R,
                               Discriminants_Only => False,
                               Loops              => Ctx.Current_Loops,
                               E_Loc              => Callsite),
                            V);
         In_List.Append (V);
      end loop;

      for W of Writes loop
         if not Reads.Contains (W) then
            Atr := Make_Global_Attributes
              (Call_Vertex        => Callsite,
               Global             => Change_Variant (W, In_View),
               Discriminants_Only => True,
               Loops              => Ctx.Current_Loops,
               E_Loc              => Callsite);
            if Atr.Variables_Used.Length >= 1 then
               FA.CFG.Add_Vertex (Atr, V);
               In_List.Append (V);
            end if;
         end if;
         FA.CFG.Add_Vertex (Make_Global_Attributes
                              (Call_Vertex        => Callsite,
                               Global             => W,
                               Discriminants_Only => False,
                               Loops              => Ctx.Current_Loops,
                               E_Loc              => Callsite),
                            V);
         Out_List.Append (V);
      end loop;

   end Process_Subprogram_Globals;

   --------------------------------------
   --  Process_Parameter_Associations  --
   --------------------------------------

   procedure Process_Parameter_Associations
     (L                 : List_Id;
      Called_Subprogram : Entity_Id;
      In_List           : in out Vertex_Vectors.Vector;
      Out_List          : in out Vertex_Vectors.Vector;
      FA                : in out Flow_Analysis_Graphs;
      CM                : in out Connection_Maps.Map;
      Ctx               : in out Context)
   is
      pragma Unreferenced (CM);

      P      : Node_Id;

      V      : Flow_Graphs.Vertex_Id;

      Actual : Node_Id;
      Formal : Node_Id;
      Call   : Node_Id;
      Atr    : V_Attributes;
   begin
      --  Create initial nodes for the statements.
      P := First (L);
      while Present (P) loop
         case Nkind (P) is
            when N_Parameter_Association =>
               --  F (A => B)
               Actual := Explicit_Actual_Parameter (P);
               Find_Actual (Actual, Formal, Call);
               pragma Assert (Entity (Name (Call)) = Called_Subprogram);

            when others =>
               --  F (B)
               Actual := P;
               Find_Actual (Actual, Formal, Call);
               pragma Assert (Entity (Name (Call)) = Called_Subprogram);
         end case;

         pragma Assert (Ekind (Formal) = E_In_Parameter or
                          Ekind (Formal) = E_In_Out_Parameter or
                          Ekind (Formal) = E_Out_Parameter);

         --  Build an in vertex.
         if Ekind (Formal) = E_In_Parameter or
           Ekind (Formal) = E_In_Out_Parameter then
            FA.CFG.Add_Vertex
              (Direct_Mapping_Id (P, In_View),
               Make_Parameter_Attributes
                 (Call_Vertex        => Parent (L),
                  Actual             => Actual,
                  Formal             => Formal,
                  In_Vertex          => True,
                  Discriminants_Only => False,
                  Loops              => Ctx.Current_Loops,
                  E_Loc              => P),
               V);
            In_List.Append (V);
         elsif Ekind (Formal) = E_Out_Parameter then
            Atr := Make_Parameter_Attributes
              (Call_Vertex        => Parent (L),
               Actual             => Actual,
               Formal             => Formal,
               In_Vertex          => True,
               Discriminants_Only => True,
               Loops              => Ctx.Current_Loops,
               E_Loc              => P);
            if Atr.Variables_Used.Length >= 1 then
               FA.CFG.Add_Vertex
                 (Direct_Mapping_Id (P, In_View), Atr, V);
               In_List.Append (V);
            end if;
         end if;

         --  Build an out vertex.
         if Ekind (Formal) = E_In_Out_Parameter or
           Ekind (Formal) = E_Out_Parameter then
            FA.CFG.Add_Vertex
              (Direct_Mapping_Id (P, Out_View),
               Make_Parameter_Attributes
                 (Call_Vertex        => Parent (L),
                  Actual             => Actual,
                  Formal             => Formal,
                  In_Vertex          => False,
                  Discriminants_Only => False,
                  Loops              => Ctx.Current_Loops,
                  E_Loc              => P),
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
              N_Label                           |
              N_Implicit_Label_Declaration      |
              N_Subprogram_Body                 |
              N_Subprogram_Declaration          |
              N_Package_Declaration             |  -- ??? remove in M314-014
              N_Package_Body                    |  -- ??? remove in M314-014
              N_Generic_Subprogram_Declaration  |
              N_Generic_Package_Declaration     |
              N_Representation_Clause           |
              N_Package_Body_Stub               |
              N_Generic_Instantiation           |
              N_Subprogram_Body_Stub            |
              N_Incomplete_Type_Declaration     |
              N_Use_Package_Clause              |
              N_Use_Type_Clause                 |
              N_Object_Renaming_Declaration     |
              N_Subprogram_Renaming_Declaration |
              N_Validate_Unchecked_Conversion   |
              N_Package_Renaming_Declaration    |
              N_Private_Type_Declaration        |
              N_Number_Declaration =>
               --  We completely skip these.
               null;

            when others =>
               Process_Statement (P, FA, CM, Ctx);
               Statement_List.Append (Union_Id (P));

         end case;
         P := Next (P);
      end loop;

      --  Produce the joined up list.
      Join (CFG   => FA.CFG,
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
   begin
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
         when N_If_Statement =>
            Do_If_Statement (N, FA, CM, Ctx);
         when N_Loop_Statement =>
            Do_Loop_Statement (N, FA, CM, Ctx);
         when N_Null_Statement =>
            Do_Null_Or_Raise_Statement (N, FA, CM, Ctx);
         when N_Object_Declaration =>
            Do_Object_Declaration (N, FA, CM, Ctx);
         when N_Pragma =>
            Do_Pragma (N, FA, CM, Ctx);
         when N_Procedure_Call_Statement =>
            --  Check for aliasing first
            Check_Procedure_Call (N, FA.Aliasing_Present);

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
   end Process_Statement;

   ----------------
   --  Simplify  --
   ----------------

   procedure Simplify (G : in out Flow_Graphs.T'Class) is
      A : V_Attributes;
   begin
      for V of G.Get_Collection (Flow_Graphs.All_Vertices) loop
         if G.Get_Attributes (V).Is_Null_Node then
            --  Close the subgraph indicated by V's neighbours.
            for A of G.Get_Collection (V, Flow_Graphs.In_Neighbours) loop
               for B of G.Get_Collection (V, Flow_Graphs.Out_Neighbours) loop
                  G.Add_Edge (A, B, EC_Default);
               end loop;
            end loop;

            --  Remove all edges from the vertex.
            G.Clear_Vertex (V);

            --  Clear the Is_Program_Node flag.
            A := G.Get_Attributes (V);
            A.Is_Program_Node := False;
            G.Set_Attributes (V, A);
         end if;
      end loop;
   end Simplify;

   -----------------------------
   -- Pragma_Relevant_To_Flow --
   -----------------------------

   function Pragma_Relevant_To_Flow (N : Node_Id) return Boolean
   is
   begin
      case Get_Pragma_Id (N) is
         when Pragma_Abstract_State               |
              Pragma_Ada_05                       |
              Pragma_Ada_12                       |
              Pragma_Ada_2005                     |
              Pragma_Ada_2012                     |
              Pragma_Ada_83                       |
              Pragma_Ada_95                       |
              Pragma_Annotate                     |
              Pragma_Assertion_Policy             |
              Pragma_Check_Policy                 |
              Pragma_Contract_Cases               |
              Pragma_Convention                   |
              Pragma_Depends                      |
              Pragma_Elaborate                    |
              Pragma_Elaborate_All                |
              Pragma_Elaborate_Body               |
              Pragma_Export                       |
              Pragma_Global                       |
              Pragma_Import                       |
              Pragma_Initial_Condition            |
              Pragma_Initializes                  |
              Pragma_Inline                       |
              Pragma_Inline_Always                |
              Pragma_Overflow_Mode                |
              Pragma_Pack                         |
              Pragma_Postcondition                |
              Pragma_Precondition                 |
              Pragma_Preelaborable_Initialization |
              Pragma_Preelaborate                 |
              Pragma_Pure                         |
              Pragma_Pure_Function                |
              Pragma_Refined_Depends              |
              Pragma_Refined_Global               |
              Pragma_Refined_State                |
              Pragma_SPARK_Mode                   |
              Pragma_Test_Case                    |
              Pragma_Warnings                     =>

            return False;

         when Pragma_Check        |
              Pragma_Loop_Variant =>

            if Get_Pragma_Id (N) = Pragma_Check and then
              Is_Precondition_Check (N)
            then
               return False;
            else
               return True;
            end if;

         when Pragma_Unmodified   |
              Pragma_Unreferenced =>
            return True;

         when others =>
            Errout.Error_Msg_Name_1 := Pragma_Name (N);
            Errout.Error_Msg_N
              ("?pragma % is not yet supported in flow analysis", N);
            Errout.Error_Msg_N ("\\ it is currently ignored", N);
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
      Body_N          : Node_Id;
      Spec_N          : Node_Id;
      Tracefile       : Unbounded_String;
   begin
      pragma Assert (Is_Valid (FA));

      case FA.Kind is
         when E_Subprogram_Body =>
            Body_N        := Get_Subprogram_Body (FA.Analyzed_Entity);
            Preconditions := Get_Precondition_Expressions (FA.Analyzed_Entity);

            FA.Depends_N := Get_Pragma (FA.Analyzed_Entity,
                                        Pragma_Depends);

            if Acts_As_Spec (Body_N) then
               Subprogram_Spec := Defining_Unit_Name (Specification (Body_N));
               FA.Refined_Depends_N :=
                 Get_Pragma (FA.Analyzed_Entity, Pragma_Refined_Depends);
            else
               Subprogram_Spec := Corresponding_Spec (Body_N);
               FA.Refined_Depends_N :=
                 Get_Pragma (Get_Body (FA.Analyzed_Entity),
                             Pragma_Refined_Depends);
            end if;

         when E_Package =>
            Spec_N := FA.Scope;
            Body_N := Spec_N;

         when E_Package_Body =>
            Body_N := FA.Scope;
            Spec_N := Get_Enclosing_Scope (Corresponding_Spec (Body_N));
      end case;

      --  Create the magic start and end vertices.
      declare
         Start_Atr : V_Attributes := Null_Attributes;
      begin
         --  We attach the subprogram's location to the start vertex
         --  as it gives us a convenient way to generate error
         --  messages applying to the whole subprogram/package/body.
         Start_Atr.Error_Location := Body_N;
         FA.CFG.Add_Vertex (Start_Atr, FA.Start_Vertex);
      end;
      FA.CFG.Add_Vertex (Null_Attributes, FA.End_Vertex);

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
            declare
               type G_Prop is record
                  Is_Read  : Boolean;
                  Is_Write : Boolean;
               end record;

               package Global_Maps is new Ada.Containers.Hashed_Maps
                 (Key_Type        => Flow_Id,
                  Element_Type    => G_Prop,
                  Hash            => Hash,
                  Equivalent_Keys => "=",
                  "="             => "=");

               Reads   : Flow_Id_Sets.Set;
               Writes  : Flow_Id_Sets.Set;
               Globals : Global_Maps.Map := Global_Maps.Empty_Map;
            begin
               Get_Globals (Subprogram   => Subprogram_Spec,
                            Reads        => Reads,
                            Writes       => Writes,
                            Refined_View => True);
               for G of Reads loop
                  Globals.Include (Change_Variant (G, Normal_Use),
                                   G_Prop'(Is_Read  => True,
                                           Is_Write => False));
               end loop;
               for G of Writes loop
                  declare
                     P : G_Prop;
                  begin
                     if Globals.Contains (Change_Variant (G, Normal_Use)) then
                        P := Globals (Change_Variant (G, Normal_Use));
                        P.Is_Write := True;
                     else
                        P := G_Prop'(Is_Read  => False,
                                     Is_Write => True);
                     end if;
                     Globals.Include (Change_Variant (G, Normal_Use), P);

                     --  If we are dealing with a function, since we found a
                     --  global output, we raise an error.
                     if Ekind (FA.Analyzed_Entity) = E_Function then
                        Error_Msg_Flow
                          (FA  => FA,
                           Tracefile => Tracefile,
                           Msg       => "function with output global & " &
                             "is not allowed in SPARK",
                           N   => FA.Analyzed_Entity,
                           F1  => G,
                           Tag => "side_effects");

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
                     else
                        raise Program_Error;
                     end if;

                     Create_Initial_And_Final_Vertices (G, Mode, False, FA);
                  end;
               end loop;
            end;

         when E_Package | E_Package_Body =>
            --  Packages have no obvious globals, but we can extract a
            --  list of global variables used from the optional rhs of
            --  the initialises clause:
            --
            --     Initializes => (State => (Global_A, ...),
            --
            --  Any other use of non-local variables is not legal (SRM
            --  7.1.5, verification rule 12).
            --
            --  Any such globals are global inputs *only* as packages
            --  are only allowed to initialise their own state.
            declare
               Initializes_Contract : constant Node_Id :=
                 (if FA.Kind = E_Package
                  then Get_Pragma (FA.Analyzed_Entity, Pragma_Initializes)
                  else Get_Pragma (Spec_Entity (FA.Analyzed_Entity),
                                   Pragma_Initializes));

               Global_Ins : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
               --  We need to make sure to only add each global once
               --  (an entity might be used to derive more than one of
               --  our states).
            begin
               if Present (Initializes_Contract) then
                  for Opt_In of Parse_Initializes (Initializes_Contract) loop
                     if Opt_In.Exists then
                        for G of Opt_In.The_Set loop
                           if not Global_Ins.Contains (G) then
                              Global_Ins.Include (G);
                              Create_Initial_And_Final_Vertices
                                (F             => G,
                                 Mode          => Mode_In,
                                 Uninitialized =>
                                   not Is_Initialized_At_Elaboration
                                   (Get_Direct_Mapping_Id (G)),
                                 FA            => FA);
                           end if;
                        end loop;
                     end if;
                  end loop;
               end if;
            end;

      end case;

      --  Collect variables introduced by quantified expressions. We
      --  need to look at the following parts:
      --     - precondition
      --     - declarative part
      --     - body
      case FA.Kind is
         when E_Subprogram_Body =>
            for Precondition of Preconditions loop
               Process_Quantified_Expressions
                 (Precondition, FA, Connection_Map, The_Context);
            end loop;
            Process_Quantified_Expressions
              (Declarations (Body_N), FA, Connection_Map, The_Context);
            Process_Quantified_Expressions
              (Statements (Handled_Statement_Sequence (Body_N)),
               FA, Connection_Map, The_Context);

         when E_Package =>
            --  !!! Look into initial conditions
            Process_Quantified_Expressions
              (Visible_Declarations (Spec_N), FA, Connection_Map, The_Context);
            Process_Quantified_Expressions
              (Private_Declarations (Spec_N), FA, Connection_Map, The_Context);

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

      end case;

      --  If we are dealing with a function, we use its entity to deal
      --  with the value returned.
      if Ekind (FA.Analyzed_Entity) = E_Function then
         Create_Initial_And_Final_Vertices (FA.Analyzed_Entity, False, FA);
      end if;

      --  If you're now wondering where we deal with locally declared
      --  objects; we deal with them as they are encountered. See
      --  Do_N_Object_Declaration for enlightenment.

      --  Produce flowgraph for the precondition, if any.
      case FA.Kind is
         when E_Subprogram_Body =>
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
               Join (CFG   => FA.CFG,
                     CM    => Connection_Map,
                     Nodes => NL,
                     Block => Precon_Block);
            end;

         when E_Package | E_Package_Body =>
            --  !!! process initial condition
            null;
      end case;

      --  Produce flowgraphs for the body and link to start and end
      --  vertex.
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
                       FA.End_Vertex);

            end;
      end case;

      --  Simplify graph by removing all null vertices.
      Simplify (FA.CFG);
   end Create;

end Flow.Control_Flow_Graph;
