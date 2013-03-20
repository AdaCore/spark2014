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

with Nlists;   use Nlists;
with Sem_Eval; use Sem_Eval;
with Sem_Util; use Sem_Util;
with Snames;   use Snames;

with Treepr;   use Treepr;

with Flow.Debug; use Flow.Debug;
pragma Unreferenced (Flow.Debug);

with Flow.Control_Flow_Graph.Utility;
use Flow.Control_Flow_Graph.Utility;

with Why;

package body Flow.Control_Flow_Graph is

   use type Flow_Graphs.Vertex_Id;

   use Vertex_Sets;
   use type Flow_Id_Sets.Set;
   use type Node_Sets.Set;

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
      Current_Loops : Node_Sets.Set;
   end record;

   No_Context : constant Context :=
     Context'(Current_Loops => Node_Sets.Empty_Set);

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

   procedure Create_Initial_And_Final_Vertices
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs);
   --  Create the 'initial and 'final vertices for the given entity
   --  and link them up to the start and end vertices.

   procedure Create_Initial_And_Final_Vertices
     (F    : Flow_Id;
      Mode : Global_Modes;
      FA   : in out Flow_Analysis_Graphs);
   --  Create the 'initial and 'final vertices for the given global
   --  and link them up to the start and end vertices.

   function Flatten_Variable (E : Entity_Id) return Flow_Id_Sets.Set;
   --  Returns a set of flow_ids for all parts of the unique entity
   --  for E. For records this includes all subcomponents, for
   --  everything else this is just the variable E.

   function All_Record_Components
     (Entire_Var : Entity_Id)
      return Flow_Id_Sets.Set
      with Pre => Ekind (Etype (Entire_Var)) = E_Record_Type;
   --  Given the record Entire_Var, return a set with all components.
   --  So, for example we might return:
   --     * p.x
   --     * p.r.a
   --     * p.r.b

   function All_Record_Components
     (The_Record_Field : Flow_Id)
      return Flow_Id_Sets.Set
      with Pre => The_Record_Field.Kind in Direct_Mapping | Record_Field
                  and then Ekind (Etype
                                    (Get_Direct_Mapping_Id
                                       (The_Record_Field))) = E_Record_Type;
   --  As above but only include fields that are equal to Record_Field or are
   --  nested under it. For example if Record_Field = p.r for the above
   --  record, then we will get the following set:
   --     * p.r.a
   --     * p.r.b

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

   procedure Do_Full_Type_Declaration
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Full_Type_Declaration;
   --  ??? to be implemented

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
                   Identifier (N) /= Empty,
           Post => Ctx.Current_Loops.Length = Ctx.Current_Loops'Old.Length;
   --  Deals with all three kinds of loops SPARK supports:
   --
   --     * for loops
   --     * while loops
   --     * (infinite) loops
   --
   --  Refer to the documentation of the nested procedures on how the
   --  constructed CFG will look like.

   procedure Do_Null_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Null_Statement;
   --  Deals with null statements. We create a new vertex that has control
   --  flow in from the top and leave from the bottom (nothing happens in
   --  between).

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
   --  The following pragmas are simply ignored:
   --    Pragma_Annotate
   --    Pragma_Depends       (we deal with this separately)
   --    Pragma_Export
   --    Pragma_Global        (we deal with this separately)
   --    Pragma_Import
   --    Pragma_Preelaborate
   --    Pragma_Pure
   --    Pragma_Warnings

   --  The following pragmas are checked for uninitialized variables:
   --    Pragma_Check
   --    Pragma_Loop_Variant
   --    Pragma_Precondition
   --    Pragma_Postcondition
   --
   --  Any other pragmas will raise Why.Not_Implemented.

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
      with Pre => Nkind (N) in N_Subprogram_Body | N_Block_Statement;
   --  This is the top level procedure which deals with a subprogam or
   --  a block statement. The declarations and sequence of statements
   --  is processed and linked.

   procedure Do_Representation_Clause
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) in N_Representation_Clause;
   --  This deals with representation clauses. More specifically,
   --  the following nodes are ignored:
   --    N_At_Clause
   --    N_Component
   --    N_Enumeration_Representation_Clause
   --    N_Mod_Clause
   --    N_Record_Representation_Clause
   --  while the following nodes raise why.Not_SPARK:
   --    N_Attribute_Definition_Clause

   procedure Process_Quantified_Expressions
     (L   : List_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context);
   --  This procedure goes through a given list of statements and
   --  recursively looks at each one, setting up the 'initial and
   --  'final vertices for symbols introduced by quantified
   --  expressions. We do not descend into nested subprograms.

   procedure Process_Subprogram_Globals
     (Callsite          : Node_Id;
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

   ---------------------------------------
   -- Create_Initial_And_Final_Vertices --
   ----------------------------------------

   procedure Create_Initial_And_Final_Vertices
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs)
   is
      V : Flow_Graphs.Vertex_Id;
   begin

      for F of Flatten_Variable (E) loop
         --  Setup the n'initial vertex. Note that initialisation for
         --  variables is detected (and set) when building the flow graph
         --  for declarative parts.
         FA.CFG.Add_Vertex
           (Change_Variant (F, Initial_Value),
            Make_Variable_Attributes (F_Ent => Change_Variant
                                        (F, Initial_Value),
                                      E_Loc => E),
            V);
         Linkup (FA.CFG, V, FA.Start_Vertex);

         --  Setup the n'final vertex.
         FA.CFG.Add_Vertex
           (Change_Variant (F, Final_Value),
            Make_Variable_Attributes (F_Ent => Change_Variant
                                        (F, Final_Value),
                                      E_Loc => E),
            V);
         Linkup (FA.CFG, FA.End_Vertex, V);

         FA.All_Vars.Include (F);
      end loop;
   end Create_Initial_And_Final_Vertices;

   procedure Create_Initial_And_Final_Vertices
     (F    : Flow_Id;
      Mode : Global_Modes;
      FA   : in out Flow_Analysis_Graphs)
   is
      V : Flow_Graphs.Vertex_Id;
   begin
      --  Setup the n'initial vertex. Initialisation is deduced from
      --  the mode.
      FA.CFG.Add_Vertex
        (Change_Variant (F, Initial_Value),
         Make_Global_Variable_Attributes
           (F    => Change_Variant (F, Initial_Value),
            Mode => Mode),
         V);
      Linkup (FA.CFG, V, FA.Start_Vertex);

      --  Setup the n'final vertex.
      FA.CFG.Add_Vertex
        (Change_Variant (F, Final_Value),
         Make_Global_Variable_Attributes
           (F    => Change_Variant (F, Final_Value),
            Mode => Mode),
         V);
      Linkup (FA.CFG, FA.End_Vertex, V);

      FA.All_Vars.Include (F);
   end Create_Initial_And_Final_Vertices;

   ----------------------
   -- Flatten_Variable --
   ----------------------

   function Flatten_Variable (E : Entity_Id) return Flow_Id_Sets.Set
   is
      U : constant Entity_Id := Unique_Entity (E);
   begin
      case Ekind (Etype (U)) is
         when Elementary_Kind | Array_Kind =>
            return Flow_Id_Sets.To_Set (Direct_Mapping_Id (U));

         when E_Record_Type =>
            return All_Record_Components (Entire_Var => U);

         when others =>
            Print_Node_Briefly (Etype (E));
            raise Why.Not_Implemented;
      end case;
   end Flatten_Variable;

   ---------------------------
   -- All_Record_Components --
   ---------------------------

   function All_Record_Components
     (Entire_Var : Entity_Id)
      return Flow_Id_Sets.Set
   is
   begin
      return All_Record_Components (Direct_Mapping_Id (Entire_Var));
   end All_Record_Components;

   function All_Record_Components
     (The_Record_Field : Flow_Id)
      return Flow_Id_Sets.Set
   is
      Entire_Var : constant Entity_Id :=
        Get_Direct_Mapping_Id (The_Record_Field);

      All_Comp   : Flow_Id_Sets.Set   := Flow_Id_Sets.Empty_Set;

      procedure Possibly_Include (F : Flow_Id);
      --  Include F in All_Comp if it is The_Record_Field or a
      --  subcomponent of it.

      procedure Process_Record (R_Type : Entity_Id;
                                Comp   : Entity_Lists.Vector)
      with Pre => Ekind (R_Type) = E_Record_Type;
      --  Recursively go through the record's components, adding
      --  everything to All_Comp.

      procedure Possibly_Include (F : Flow_Id)
      is
      begin
         --  ??? Direct access into flow_id, should be removed somehow.
         if F.Component.Length < The_Record_Field.Component.Length then
            return;
         end if;

         for I in Natural
           range 1 .. Natural (The_Record_Field.Component.Length)
         loop
            if The_Record_Field.Component (I) /= F.Component (I) then
               return;
            end if;
         end loop;

         All_Comp.Include (F);
      end Possibly_Include;

      procedure Process_Record (R_Type : Entity_Id;
                                Comp   : Entity_Lists.Vector)
      is
         C : Entity_Id;
         F : Flow_Id;
      begin
         --  Make a vertex for each subcomponent, unless its a
         --  record. If we have a record we recurse instead.
         C := First_Component (R_Type);
         while C /= Empty loop
            declare
               Tmp : Entity_Lists.Vector := Comp;
            begin
               Tmp.Append (C);

               case Ekind (Etype (C)) is
                  when E_Record_Type =>
                     Process_Record (Etype (C), Tmp);

                  when others =>
                     F := Flow_Id'(Kind      => Record_Field,
                                   Variant   => Normal_Use,
                                   Node      => Entire_Var,
                                   Name      => Null_Entity_Name,
                                   Component => Tmp);
                     Possibly_Include (F);
               end case;
            end;

            C := Next_Component (C);
         end loop;
      end Process_Record;

   begin
      Process_Record (Etype (Entire_Var),
                      Entity_Lists.Empty_Vector);
      return All_Comp;
   end All_Record_Components;

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
      V_Used_RHS := Get_Variable_Set (Expression (N));

      Untangle_Assignment_Target (N            => Name (N),
                                  Vars_Used    => V_Used_LHS,
                                  Vars_Defined => V_Def_LHS);

      --  Print the node and its def-use effect
      --  Print_Node_Subtree (N);
      --  Print_Node_Set (V_Def_LHS);
      --  Print_Node_Set (V_Used_LHS or V_Used_RHS or V_Also_Used);

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
                                  (Expression (N)),
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
      if Name (N) = Empty then
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
      if Condition (N) = Empty then
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
            Make_Basic_Attributes (Var_Use => Get_Variable_Set (Condition (N)),
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

   --------------------------------
   --  Do_Full_Type_Declaration  --
   --------------------------------

   procedure Do_Full_Type_Declaration
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
   begin
      raise Why.Not_Implemented;
   end Do_Full_Type_Declaration;

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
      --  !!! Workaround
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
         Make_Basic_Attributes (Var_Use => Get_Variable_Set (Condition (N)),
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
                                           (Condition (Elsif_Statement)),
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
      V : Flow_Graphs.Vertex_Id;

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
            --  !!! workaround
            CM (Union_Id (N)).Standard_Exits.Union
              (CM.Element (Union_Id (Statements (N))).Standard_Exits);
         end if;

         --  Loop the loop: V -> body -> V
         Linkup (FA.CFG, V, CM (Union_Id (Statements (N))).Standard_Entry);
         Linkup (FA.CFG, CM (Union_Id (Statements (N))).Standard_Exits, V);
      end Do_Loop;

      procedure Do_While_Loop is
      begin
         FA.CFG.Add_Vertex
           (Direct_Mapping_Id (N),
            Make_Basic_Attributes (Var_Use => Get_Variable_Set
                                     (Condition (Iteration_Scheme (N))),
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

      procedure Do_For_Loop is
         LPS : constant Node_Id :=
           Loop_Parameter_Specification (Iteration_Scheme (N));

         LP : constant Entity_Id := Defining_Identifier (LPS);

         DSD : constant Node_Id := Discrete_Subtype_Definition (LPS);

         R : Node_Id;
      begin
         case Nkind (DSD) is
            when N_Subtype_Indication =>
               case Nkind (Constraint (DSD)) is
                  when N_Range_Constraint =>
                     R := Range_Expression (Constraint (DSD));
                  when others =>
                     raise Why.Not_Implemented;
               end case;
            when N_Range =>
               R := DSD;
            when others =>
               Print_Node_Subtree (DSD);
               raise Why.Not_Implemented;
         end case;

         --  We have a new variable here which we have not picked up
         --  in Create, so we should set it up.
         Create_Initial_And_Final_Vertices (LP, FA);

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
                  Var_Use => Get_Variable_Set (DSD),
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
      Process_Statement_List (Statements (N), FA, CM, Ctx);
      Ctx.Current_Loops.Delete (Entity (Identifier (N)));

      if Iteration_Scheme (N) = Empty then
         --  We have a loop.
         Do_Loop;

      else
         --  We have either a while loop or a for loop.

         --  We have a vertex for the loop condition, depending on its
         --  iteration scheme.
         if Condition (Iteration_Scheme (N)) /= Empty then
            --  We have a while loop.
            Do_While_Loop;

         elsif Iterator_Specification (Iteration_Scheme (N)) /= Empty then
            --  N_Iterator_Specification is not in SPARK2014
            raise Why.Not_Implemented;

         else
            --  We have a for loop. Make sure we don't have an
            --  iterator, but a normal range.
            pragma Assert (Loop_Parameter_Specification (Iteration_Scheme (N))
                             /= Empty);

            Do_For_Loop;
         end if;
      end if;
   end Do_Loop_Statement;

   -------------------------
   --  Do_Null_Statement  --
   -------------------------

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
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (N),
         Make_Aux_Vertex_Attributes (E_Loc => N),
         V);
      CM.Include (Union_Id (N), No_Connections);
      CM (Union_Id (N)).Standard_Entry := V;
      CM (Union_Id (N)).Standard_Exits.Insert (V);
   end Do_Null_Statement;

   -----------------------------
   --  Do_Object_Declaration  --
   -----------------------------

   procedure Do_Object_Declaration
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      V : Flow_Graphs.Vertex_Id;
   begin
      --  First, we need a 'initial and 'final vertex for this object.
      Create_Initial_And_Final_Vertices (Defining_Identifier (N), FA);

      if Expression (N) = Empty then
         --  Just a null vertex.
         FA.CFG.Add_Vertex (Direct_Mapping_Id (N),
                            Null_Node_Attributes,
                            V);
      else
         --  We have a vertex
         FA.CFG.Add_Vertex
           (Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Var_Def => Flatten_Variable (Defining_Identifier (N)),
               Var_Use => Get_Variable_Set (Expression (N)),
               Loops   => Ctx.Current_Loops,
               E_Loc   => N),
            V);
      end if;
      CM.Include (Union_Id (N),
                  Graph_Connections'(Standard_Entry => V,
                                     Standard_Exits => To_Set (V)));
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
      pragma Unreferenced (Ctx);
      V : Flow_Graphs.Vertex_Id;
   begin
      case Get_Pragma_Id (Pragma_Name (N)) is
         when Pragma_Annotate     |
              Pragma_Depends      |
              Pragma_Export       |
              Pragma_Global       |
              Pragma_Import       |
              Pragma_Preelaborate |
              Pragma_Pure         |
              Pragma_Warnings     =>

            --  We create a null vertex for the pragma.
            FA.CFG.Add_Vertex (Direct_Mapping_Id (N),
                               Null_Node_Attributes,
                               V);
            CM.Include (Union_Id (N), No_Connections);
            CM (Union_Id (N)).Standard_Entry := V;
            CM (Union_Id (N)).Standard_Exits := To_Set (V);

         when Pragma_Check         |
              Pragma_Loop_Variant  |
              Pragma_Precondition  |
              Pragma_Postcondition =>

            --  We create a sink vertex for the pragma (which we just
            --  use to check for uninitialized variables).
            FA.CFG.Add_Vertex
              (Direct_Mapping_Id (N),
               Make_Sink_Vertex_Attributes
                 (Var_Use => Get_Variable_Set
                    (Pragma_Argument_Associations (N)),
                  E_Loc   => N),
               V);
            CM.Include (Union_Id (N), No_Connections);
            CM (Union_Id (N)).Standard_Entry := V;
            CM (Union_Id (N)).Standard_Exits := To_Set (V);

         when Unknown_Pragma =>
            --  If we find an Unknown_Pragma we raise Why.Not_SPARK
            raise Why.Not_SPARK;

         when others =>
            raise Why.Not_Implemented;
      end case;
   end Do_Pragma;

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

   begin
      --  A vertex for the actual call.
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (N),
         Make_Call_Attributes (Callsite => N,
                               Loops    => Ctx.Current_Loops,
                               E_Loc    => N),
         V);

      --  Deal with the procedures parameters.
      Process_Parameter_Associations (Parameter_Associations (N),
                                      Called_Procedure,
                                      In_List,
                                      Out_List,
                                      FA, CM, Ctx);

      --  Process globals.
      Process_Subprogram_Globals (N,
                                  In_List, Out_List,
                                  FA, CM, Ctx);

      --  We now build the connection map for this sequence.
      declare
         use Vertex_Vectors;
         L             : constant List_Id := Parameter_Associations (N);
         Combined_List : constant Vertex_Vectors.Vector := In_List & Out_List;
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
           (Union_Id (L),
            Graph_Connections'(Standard_Entry => Combined_List.First_Element,
                               Standard_Exits => Vertex_Sets.To_Set
                                 (Combined_List.Last_Element)));
      end;

      CM.Include
        (Union_Id (N),
         Graph_Connections'(Standard_Entry => V,
                            Standard_Exits => CM.Element
                              (Union_Id
                                 (Parameter_Associations
                                    (N))).Standard_Exits));

      Linkup (FA.CFG,
              V,
              CM (Union_Id (Parameter_Associations (N))).Standard_Entry);
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
      if Expression (N) = Empty then
         --  We have a return for a procedure.
         FA.CFG.Add_Vertex (Direct_Mapping_Id (N),
                            Make_Aux_Vertex_Attributes (E_Loc => N),
                            V);
      else
         --  We have a function return.
         FA.CFG.Add_Vertex
           (Direct_Mapping_Id (N),
            Make_Basic_Attributes
              (Var_Def => Flatten_Variable (FA.Subprogram),
               Var_Use => Get_Variable_Set (Expression (N)),
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
      Process_Statement_List (Declarations (N), FA, CM, Ctx);

      Do_Handled_Sequence_Of_Statements
        (Handled_Statement_Sequence (N), FA, CM, Ctx);

      Linkup (FA.CFG,
              CM (Union_Id (Declarations (N))).Standard_Exits,
              CM (Union_Id (Handled_Statement_Sequence (N))).Standard_Entry);

      --  !!! workaround
      CM.Include
        (Union_Id (N),
         Graph_Connections'
           (Standard_Entry => CM.Element
              (Union_Id (Declarations (N))).Standard_Entry,
            Standard_Exits => CM.Element
              (Union_Id (Handled_Statement_Sequence (N))).Standard_Exits));
   end Do_Subprogram_Or_Block;

   ------------------------------
   -- Do_Representation_Clause --
   ------------------------------

   procedure Do_Representation_Clause
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
   is
      pragma Unreferenced (FA);
      pragma Unreferenced (CM);
      pragma Unreferenced (Ctx);
   begin
      if Nkind (N) = N_Attribute_Definition_Clause then
         raise Why.Not_SPARK;
      end if;
   end Do_Representation_Clause;

   ------------------------------------
   -- Process_Quantified_Expressions --
   ------------------------------------

   procedure Process_Quantified_Expressions
     (L   : List_Id;
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

            when N_Quantified_Expression =>
               --  Sanity check: Iterator_Specification is not in
               --  SPARK so it should always be empty.
               pragma Assert (No (Iterator_Specification (N)));

               Create_Initial_And_Final_Vertices
                 (Defining_Identifier (Loop_Parameter_Specification (N)),
                  FA);

            when others =>
               null;
         end case;

         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Process => Proc);

      N : Node_Id := First (L);
   begin
      while Present (N) loop
         Traverse (N);
         Next (N);
      end loop;
   end Process_Quantified_Expressions;

   --------------------------------
   -- Process_Subprogram_Globals --
   --------------------------------

   procedure Process_Subprogram_Globals
     (Callsite          : Node_Id;
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
   begin
      --  Obtain globals (either from contracts or the computerd
      --  stuff).
      Get_Globals (Subprogram => Entity (Name (Callsite)),
                   Reads      => Reads,
                   Writes     => Writes);

      for R of Reads loop
         FA.CFG.Add_Vertex (Make_Global_Attributes
                              (Call_Vertex => Callsite,
                               Global      => R,
                               Loops       => Ctx.Current_Loops,
                               E_Loc       => Callsite),
                            V);
         In_List.Append (V);
      end loop;

      for W of Writes loop
         FA.CFG.Add_Vertex (Make_Global_Attributes
                              (Call_Vertex => Callsite,
                               Global      => W,
                               Loops       => Ctx.Current_Loops,
                               E_Loc       => Callsite),
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
   begin
      --  Create initial nodes for the statements.
      P    := First (L);
      while P /= Empty loop
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

         if Ekind (Formal) = E_In_Parameter or
           Ekind (Formal) = E_In_Out_Parameter then
            --  Build an in vertex.
            FA.CFG.Add_Vertex
              (Direct_Mapping_Id (P, In_View),
               Make_Parameter_Attributes
                 (Call_Vertex => Parent (L),
                  Actual      => Actual,
                  Formal      => Formal,
                  In_Vertex   => True,
                  Loops       => Ctx.Current_Loops,
                  E_Loc       => P),
               V);
            In_List.Append (V);
         end if;

         if Ekind (Formal) = E_In_Out_Parameter or
           Ekind (Formal) = E_Out_Parameter then
            --  Build an out vertex.
            FA.CFG.Add_Vertex
              (Direct_Mapping_Id (P, Out_View),
               Make_Parameter_Attributes
                 (Call_Vertex => Parent (L),
                  Actual      => Actual,
                  Formal      => Formal,
                  In_Vertex   => False,
                  Loops       => Ctx.Current_Loops,
                  E_Loc       => P),
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
      P    : Node_Or_Entity_Id;
      Prev : Node_Or_Entity_Id;
      V    : Flow_Graphs.Vertex_Id;
   begin
      --  We need a connection map for this sequence.
      CM.Include (Union_Id (L), No_Connections);

      --  Create initial nodes for the statements.
      P    := First (L);
      Prev := Empty;
      while P /= Empty loop
         case Nkind (P) is
            when N_Freeze_Entity |
              N_Implicit_Label_Declaration |
              N_Subprogram_Body |
              N_Subprogram_Declaration =>
               --  We completely skip these.
               P := Next (P);

            when others =>
               Process_Statement (P, FA, CM, Ctx);

               --  Connect this statement to the previous one.
               if Prev /= Empty then
                  Linkup (FA.CFG,
                          CM (Union_Id (Prev)).Standard_Exits,
                          CM (Union_Id (P)).Standard_Entry);
               else
                  --  This is the first vertex, so set the standard entry
                  --  of the list.
                  CM (Union_Id (L)).Standard_Entry :=
                    CM (Union_Id (P)).Standard_Entry;
               end if;

               --  Go to the next statement
               Prev := P;
               P    := Next (P);
         end case;
      end loop;

      if Prev /= Empty then
         --  Set the standard exits of the list, if we processed at
         --  least one element.
         CM (Union_Id (L)).Standard_Exits :=
           CM (Union_Id (Prev)).Standard_Exits;
      else
         --  We had a null sequence so we need to produce a null node.
         FA.CFG.Add_Vertex (Null_Node_Attributes,
                            V);
         CM (Union_Id (L)).Standard_Entry := V;
         CM (Union_Id (L)).Standard_Exits := To_Set (V);
      end if;
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
         when N_Case_Statement =>
            Do_Case_Statement (N, FA, CM, Ctx);
         when N_Exit_Statement =>
            Do_Exit_Statement (N, FA, CM, Ctx);
         when N_Full_Type_Declaration =>
            Do_Full_Type_Declaration (N, FA, CM, Ctx);
         when N_If_Statement =>
            Do_If_Statement (N, FA, CM, Ctx);
         when N_Loop_Statement =>
            Do_Loop_Statement (N, FA, CM, Ctx);
         when N_Null_Statement =>
            Do_Null_Statement (N, FA, CM, Ctx);
         when N_Object_Declaration =>
            Do_Object_Declaration (N, FA, CM, Ctx);
         when N_Pragma =>
            Do_Pragma (N, FA, CM, Ctx);
         when N_Procedure_Call_Statement =>
            Do_Procedure_Call_Statement (N, FA, CM, Ctx);
         when N_Simple_Return_Statement =>
            Do_Simple_Return_Statement (N, FA, CM, Ctx);
         when N_Representation_Clause =>
            Do_Representation_Clause (N, FA, CM, Ctx);
         when N_Block_Statement =>
            Do_Subprogram_Or_Block (N, FA, CM, Ctx);
         when others =>
            Print_Node_Subtree (N);
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

   ------------------------------------------------------------
   --  Package functions and procedures
   ------------------------------------------------------------

   ------------------------
   --  Get_Variable_Set  --
   ------------------------

   function Get_Variable_Set (N : Node_Id) return Flow_Id_Sets.Set is
      VS     : Flow_Id_Sets.Set;

      procedure Process_Function_Call
        (Callsite       : Node_Id;
         Used_Variables : in out Flow_Id_Sets.Set)
         with Pre => Nkind (Callsite) = N_Function_Call;
      --  Work out which variables (including globals) are used in the
      --  function call and add them to the given set.

      function Proc (N : Node_Id) return Traverse_Result;
      --  Adds each identifier or defining_identifier found to VS, as
      --  long as we are dealing with:
      --     * a variable
      --     * a subprogram parameter
      --     * a loop parameter
      --     * a constant

      ---------------------------
      -- Process_Function_Call --
      ---------------------------

      procedure Process_Function_Call
        (Callsite       : Node_Id;
         Used_Variables : in out Flow_Id_Sets.Set) is

         Subprogram : constant Entity_Id := Entity (Name (Callsite));

         Global_Reads  : Flow_Id_Sets.Set;
         Global_Writes : Flow_Id_Sets.Set;

      begin
         Get_Globals (Subprogram => Subprogram,
                      Reads      => Global_Reads,
                      Writes     => Global_Writes);
         pragma Assert (Flow_Id_Sets.Length (Global_Writes) = 0);

         Used_Variables :=
           Used_Variables or
           Get_Variable_Set (Parameter_Associations (Callsite));

         for G of Global_Reads loop
            Used_Variables.Include (Change_Variant (G, Normal_Use));
         end loop;
      end Process_Function_Call;

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Procedure_Call_Statement |
              N_Subprogram_Body |
              N_Subprogram_Declaration =>
               --  If we ever get one of these we have a problem -
               --  Get_Variable_Set is only really meant to be called
               --  on expressions and not statements.
               raise Program_Error;

            when N_Function_Call =>
               Process_Function_Call (Callsite       => N,
                                      Used_Variables => VS);
               return Skip;

            when N_Identifier | N_Expanded_Name =>
               if Present (Entity (N)) then
                  case Ekind (Entity (N)) is
                     when E_Variable |
                       E_Loop_Parameter |
                       E_Out_Parameter |
                       E_In_Parameter |
                       E_In_Out_Parameter |
                       E_Constant =>
                        VS.Union (Flatten_Variable (Entity (N)));
                     when others =>
                        null;
                  end case;
               end if;

            when N_Defining_Identifier =>
               case Ekind (N) is
                  when E_Variable |
                    E_Loop_Parameter |
                    E_Out_Parameter |
                    E_In_Parameter |
                    E_In_Out_Parameter |
                    E_Constant =>
                     VS.Union (Flatten_Variable (N));
                  when others =>
                     null;
               end case;

            when N_Selected_Component | N_Indexed_Component =>
               declare
                  D, U : Flow_Id_Sets.Set;
               begin
                  Untangle_Assignment_Target (N            => N,
                                              Vars_Defined => D,
                                              Vars_Used    => U);
                  VS.Union (D);
                  VS.Union (U);
               end;
               return Skip;

            when others =>
               null;
         end case;
         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Process => Proc);
   begin
      Traverse (N);
      return VS;
   end Get_Variable_Set;

   function Get_Variable_Set (L : List_Id) return Flow_Id_Sets.Set is
      VS : Flow_Id_Sets.Set;
      P  : Node_Id;
   begin
      P := First (L);
      while P /= Empty loop
         VS.Union (Get_Variable_Set (P));

         P := Next (P);
      end loop;
      return VS;
   end Get_Variable_Set;

   --------------------------------
   -- Untangle_Assignment_Target --
   --------------------------------

   procedure Untangle_Assignment_Target
     (N            : Node_Id;
      Vars_Defined : out Flow_Id_Sets.Set;
      Vars_Used    : out Flow_Id_Sets.Set)
   is
      Bottom_Node   : Node_Id;
      End_Of_Record : Node_Id;

      procedure Find_Bottom_Node (N             : Node_Id;
                                  Bottom_Node   : out Node_Id;
                                  End_Of_Record : out Node_Id);
      --  This procedure returns the bottom node of the subtree and
      --  finds the end of the outermost record node.

      --  Let's consider the parse tree for P.R.A (I).A (J).X
      --  In the following parse tree 'i' represents an indexed
      --  component and s represents a selected component.
      --
      --                               Parse Tree
      --                                    s
      --                                   / \
      --                                  i   X
      --                                 / \
      --                                s   J
      --                               / \
      --                              i   A
      --                             / \
      --        End_Of_Record --->  s   I
      --                           / \
      --                          s   A
      --                         / \
      --      Bottom_Node --->  P   R

      function Proc (N : Node_Id) return Traverse_Result;
      --  Traverses a subtree and adds each variable found inside
      --  the expression part of an N_Indexed_Component to the
      --  Vars_Used set.

      -------------------
      -- Find_Top_Node --
      -------------------

      procedure Find_Bottom_Node (N             : Node_Id;
                                  Bottom_Node   : out Node_Id;
                                  End_Of_Record : out Node_Id)
      is
         Temp_Node : Node_Id := N;

         function Has_Prefix (N : Node_Id) return Boolean;
         --  Return True if N has attribute Prefix

         ----------------
         -- Has_Prefix --
         ----------------

         function Has_Prefix (N : Node_Id) return Boolean is
         begin
            return
              Nkind_In (N,
                N_Indexed_Component,
                N_Selected_Component);
         end Has_Prefix;
      begin
         End_Of_Record := N;
         --  Initially we set First_Non_Record to N

         while Has_Prefix (Temp_Node) loop
            if Nkind (Temp_Node) = N_Indexed_Component then
               End_Of_Record := Temp_Node;
            end if;
            --  If we find a node that is an array, we update
            --  End_Of_Record with it.

            Temp_Node := Prefix (Temp_Node);
         end loop;

         if End_Of_Record /= N then
            End_Of_Record := Prefix (End_Of_Record);
         end if;
         --  If we did actually find a node that is an array then
         --  we need to go one level further down.

         Bottom_Node := Temp_Node;
         --  Bottom_Node now holds the leftmost item of the
         --  declaration.
      end Find_Bottom_Node;

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         if Nkind (N) = N_Indexed_Component then
            Vars_Used.Union (Get_Variable_Set (Expressions (N)));
         end if;
         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Proc);
   begin
      case Nkind (N) is
         when N_Identifier | N_Expanded_Name =>
            --  X :=
            Vars_Defined := Get_Variable_Set (N);
         when N_Selected_Component | N_Indexed_Component =>
            --  R.A :=
            --  A (...) :=
            Traverse (N);
            Find_Bottom_Node (N, Bottom_Node, End_Of_Record);
            if Nkind (Parent (Bottom_Node)) = N_Selected_Component then
               Vars_Defined.Union (All_Record_Components
                 (Record_Field_Id (End_Of_Record)));
            else
               Vars_Defined.Insert (Direct_Mapping_Id (Entity
                 (Bottom_Node)));
               Vars_Used.Insert (Direct_Mapping_Id (Entity
                 (Bottom_Node)));
            end if;
         when others =>
            raise Why.Not_Implemented;
      end case;
   end Untangle_Assignment_Target;

   -------------
   -- Create --
   -------------

   procedure Create
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs)
   is
      Connection_Map  : Connection_Maps.Map;
      The_Context     : Context              := No_Context;
      Subprogram_Spec : Entity_Id;
   begin
      if Acts_As_Spec (N) then
         Subprogram_Spec := Defining_Unit_Name (Specification (N));
      else
         Subprogram_Spec := Corresponding_Spec (N);
      end if;

      --  Start with a blank slate.
      Connection_Map := Connection_Maps.Empty_Map;

      --  Create the magic start and end vertices.
      declare
         Start_Atr : V_Attributes := Null_Attributes;
      begin
         --  We attach the subprogram's location to the start vertex
         --  as it gives us a convenient way to generate error
         --  messages applying to the whole subprogram.
         Start_Atr.Error_Location := N;
         FA.CFG.Add_Vertex (Start_Atr, FA.Start_Vertex);
      end;
      FA.CFG.Add_Vertex (Null_Attributes, FA.End_Vertex);

      --  Collect parameters to this procedure and stick them into
      --  FA.Params.
      declare
         E : Entity_Id;
      begin
         E := First_Formal (Subprogram_Spec);
         while E /= Empty loop
            Create_Initial_And_Final_Vertices (E, FA);
            E := Next_Formal (E);
         end loop;
      end;

      --  Collect globals for this procedure and stick them into
      --  FA.All_Globals.
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
         Get_Globals (Subprogram => Subprogram_Spec,
                      Reads      => Reads,
                      Writes     => Writes);
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
            end;
         end loop;

         for C in Globals.Iterate loop
            declare
               G : constant Flow_Id := Global_Maps.Key (C);
               P : constant G_Prop  := Global_Maps.Element (C);

               Mode : Global_Modes;
            begin
               if P.Is_Read and P.Is_Write then
                  Mode := Global_Mode_In_Out;
               elsif P.Is_Read then
                  Mode := Global_Mode_In;
               elsif P.Is_Write then
                  Mode := Global_Mode_Out;
               else
                  raise Program_Error;
               end if;

               Create_Initial_And_Final_Vertices (G, Mode, FA);
            end;
         end loop;
      end;

      --  Collect variables introduced by quantified expressions.
      Process_Quantified_Expressions
        (Declarations (N), FA, Connection_Map, The_Context);
      Process_Quantified_Expressions
        (Statements (Handled_Statement_Sequence (N)),
         FA, Connection_Map, The_Context);

      --  If we are dealing with a function, we use its entity to deal
      --  with the value returned, so that should also go into
      --  FA.All_Vars.
      if Ekind (FA.Subprogram) = E_Function then
         Create_Initial_And_Final_Vertices (FA.Subprogram, FA);
      end if;

      --  If you're now wondering where we deal with locally declared
      --  objects; we deal with them as they are encountered. See
      --  Do_N_Object_Declaration for enlightenment.

      --  Produce flowgraph for the body
      Do_Subprogram_Or_Block (N, FA, Connection_Map, The_Context);

      --  Print_Node_Set (FA.All_Vars);

      --  Connect up the start and end vertices.
      Linkup (FA.CFG,
              FA.Start_Vertex,
              Connection_Map (Union_Id (N)).Standard_Entry);
      Linkup (FA.CFG,
              Connection_Map (Union_Id (N)).Standard_Exits,
              FA.End_Vertex);

      --  Simplify graph by removing all null vertices.
      Simplify (FA.CFG);
   end Create;

end Flow.Control_Flow_Graph;
