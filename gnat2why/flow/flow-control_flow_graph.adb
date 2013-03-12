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

with Treepr;   use Treepr;

with Flow.Debug; use Flow.Debug;
pragma Unreferenced (Flow.Debug);

with Flow.Control_Flow_Graph.Utility;
use Flow.Control_Flow_Graph.Utility;

with Why;

package body Flow.Control_Flow_Graph is

   use type Flow_Graphs.Vertex_Id;
   use type Ada.Containers.Count_Type;

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

   procedure Untangle_Assignment_Target
     (N            : Node_Id;
      Vars_Defined : out Flow_Id_Sets.Set;
      Vars_Used    : out Flow_Id_Sets.Set)
      with Pre => Nkind (N) in N_Identifier |
                               N_Selected_Component |
                               N_Indexed_Component,
           Post => Vars_Defined.Length >= 1;
   --  Given the target of an assignment (perhaps the left-hand-side
   --  of an assignment statement or an out vertex in a procedure
   --  call), work out which variables are actually set and which
   --  variables are used to determine what is set (in the case of
   --  arrays).

   procedure Do_Assignment_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Assignment_Statement;

   procedure Do_Exit_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Exit_Statement;

   procedure Do_Full_Type_Declaration
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Full_Type_Declaration;

   procedure Do_Handled_Sequence_Of_Statements
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Handled_Sequence_Of_Statements;

   procedure Do_If_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_If_Statement;

   procedure Do_Loop_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre  => Nkind (N) = N_Loop_Statement and then
                   Identifier (N) /= Empty,
           Post => Ctx.Current_Loops.Length = Ctx.Current_Loops'Old.Length;

   procedure Do_Object_Declaration
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Object_Declaration;

   procedure Do_Procedure_Call_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Procedure_Call_Statement;

   procedure Do_Simple_Return_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Simple_Return_Statement;

   procedure Do_Subprogram_Body
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context)
      with Pre => Nkind (N) = N_Subprogram_Body;

   procedure Process_Subprogram_Globals
     (Callsite          : Node_Id;
      In_List           : in out Vertex_Vectors.Vector;
      Out_List          : in out Vertex_Vectors.Vector;
      FA                : in out Flow_Analysis_Graphs;
      CM                : in out Connection_Maps.Map;
      Ctx               : in out Context);

   procedure Process_Parameter_Associations
     (L                 : List_Id;
      Called_Subprogram : Entity_Id;
      In_List           : in out Vertex_Vectors.Vector;
      Out_List          : in out Vertex_Vectors.Vector;
      FA                : in out Flow_Analysis_Graphs;
      CM                : in out Connection_Maps.Map;
      Ctx               : in out Context);

   procedure Process_Statement_List
     (L   : List_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context);

   procedure Process_Statement
     (N   : Node_Id;
      FA  : in out Flow_Analysis_Graphs;
      CM  : in out Connection_Maps.Map;
      Ctx : in out Context);

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

   --------------------------------
   -- Untangle_Assignment_Target --
   --------------------------------

   procedure Untangle_Assignment_Target
     (N            : Node_Id;
      Vars_Defined : out Flow_Id_Sets.Set;
      Vars_Used    : out Flow_Id_Sets.Set)
   is
   begin
      --  ??? Pavlos to implement :)
      null;
   end Untangle_Assignment_Target;

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

      V_Also_Used : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      --  Things used because of the limitations of flow analysis. In
      --  (A (J) := 0, A would also be used as the other elements do
      --  not change.)
   begin
      --  Work out which variables we use and define.
      V_Used_RHS := Get_Variable_Set (Expression (N));

      declare
         LHS : Node_Id renames Name (N);
      begin
         case Nkind (LHS) is
            when N_Identifier =>
               --  X :=
               V_Def_LHS := Get_Variable_Set (LHS);
            when N_Selected_Component =>
               --  R.A :=
               V_Def_LHS := Get_Variable_Set (LHS);
            when N_Indexed_Component =>
               --  R.A (...) :=
               V_Def_LHS  := Get_Variable_Set (Prefix (LHS));
               V_Used_LHS := Get_Variable_Set (Expressions (LHS));
               V_Also_Used := V_Def_LHS;
               raise Why.Not_Implemented;
            when others =>
               raise Why.Not_Implemented;
         end case;
      end;

      --  Print the node and its def-use effect
      --  Print_Node_Subtree (N);
      --  Print_Node_Set (V_Def_LHS);
      --  Print_Node_Set (V_Used_LHS or V_Used_RHS or V_Also_Used);

      --  We have a vertex
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (N),
         Make_Basic_Attributes (Var_Def => V_Def_LHS,
                                Var_Use => V_Used_RHS or
                                  V_Used_LHS or
                                  V_Also_Used,
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
         Unused          : Traverse_Final_Result;
         pragma Unreferenced (Unused);

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

         function Find_Return is new Traverse_Func (Process => Proc);
      begin
         --  Check if we have a return statement.
         Unused := Find_Return (N);

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
                            Make_Return_Attributes (E_Loc => N),
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

   --------------------------
   --  Do_Subprogram_Body  --
   --------------------------

   procedure Do_Subprogram_Body
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
   end Do_Subprogram_Body;

   --------------------------------
   -- Process_Subprogram_Globals --
   --------------------------------

   procedure Process_Subprogram_Globals
     (Callsite          : Node_Id;
      In_List           : in out Vertex_Vectors.Vector;
      Out_List          : in out Vertex_Vectors.Vector;
      FA                : in out Flow_Analysis_Graphs;
      CM                : in out Connection_Maps.Map;
      Ctx               : in out Context) is

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
         when N_Exit_Statement =>
            Do_Exit_Statement (N, FA, CM, Ctx);
         when N_Full_Type_Declaration =>
            Do_Full_Type_Declaration (N, FA, CM, Ctx);
         when N_If_Statement =>
            Do_If_Statement (N, FA, CM, Ctx);
         when N_Loop_Statement =>
            Do_Loop_Statement (N, FA, CM, Ctx);
         when N_Object_Declaration =>
            Do_Object_Declaration (N, FA, CM, Ctx);
         when N_Procedure_Call_Statement =>
            Do_Procedure_Call_Statement (N, FA, CM, Ctx);
         when N_Simple_Return_Statement =>
            Do_Simple_Return_Statement (N, FA, CM, Ctx);
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

            when N_Identifier =>
               if Entity (N) /= Empty then
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

   -------------
   -- Create --
   -------------

   procedure Create
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs)
   is
      Connection_Map : Connection_Maps.Map;

      The_Context    : Context          := No_Context;

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
      Do_Subprogram_Body (N, FA, Connection_Map, The_Context);

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
