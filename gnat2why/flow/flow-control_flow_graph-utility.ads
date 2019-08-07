------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--      F L O W . C O N T R O L _ F L O W _ G R A P H . U T I L I T Y       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2013-2019, Altran UK Limited                --
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

--  This package contains a few helper functions for CFG construction.

with Flow_Refinement;             use Flow_Refinement;
with Flow_Utility.Initialization; use Flow_Utility.Initialization;
with Sinfo;                       use Sinfo;
with SPARK_Util;                  use SPARK_Util;

package Flow.Control_Flow_Graph.Utility is

   function Make_Basic_Attributes
     (Var_Def    : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Var_Ex_Use : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Var_Im_Use : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Sub_Called : Node_Sets.Set       := Node_Sets.Empty_Set;
      Loops      : Node_Sets.Set       := Node_Sets.Empty_Set;
      E_Loc      : Node_Or_Entity_Id   := Empty;
      Print_Hint : Pretty_Print_Kind_T := Pretty_Print_Null)
      return V_Attributes
      with Post => not Make_Basic_Attributes'Result.Is_Null_Node and
                   Make_Basic_Attributes'Result.Is_Program_Node;
   --  Create attributes for vertices which simply define and use some
   --  variables.

   function Make_Extended_Return_Attributes
     (Var_Def         : Flow_Id_Sets.Set;
      Var_Use         : Flow_Id_Sets.Set;
      Object_Returned : Entity_Id;
      Loops           : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc           : Node_Or_Entity_Id := Empty)
      return V_Attributes
   with Pre  => Is_Return_Object (Object_Returned),
        Post =>
      not Make_Extended_Return_Attributes'Result.Is_Null_Node and
      Make_Extended_Return_Attributes'Result.Is_Program_Node and
      Make_Extended_Return_Attributes'Result.Aux_Node = Object_Returned;
   --  Create attributes for the implicit return of an extended return
   --  statement.

   function Make_Sink_Vertex_Attributes
     (Var_Use       : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Sub_Called    : Node_Sets.Set     := Node_Sets.Empty_Set;
      Aspect        : Type_Aspect       := No_Aspect;
      Is_Assertion  : Boolean           := False;
      Is_Loop_Entry : Boolean           := False;
      Is_Fold_Check : Boolean           := False;
      Is_Type_Decl  : Boolean           := False;
      E_Loc         : Node_Or_Entity_Id := Empty;
      Execution     : Execution_Kind_T  := Normal_Execution)
      return V_Attributes
   with Pre  => (if Aspect = DIC then Is_Assertion),
        Post => not Make_Sink_Vertex_Attributes'Result.Is_Null_Node and
                not Make_Sink_Vertex_Attributes'Result.Is_Program_Node;
   --  Create attributes for vertices modelling the following
   --  constructs:
   --
   --     * pragmas
   --     * aux checks for expressions containing folded functions
   --
   --  If Is_Type_Decl is True then instead of populating the variables used
   --  we populate the variables read.

   function Make_Aux_Vertex_Attributes
     (E_Loc     : Node_Or_Entity_Id := Empty;
      Execution : Execution_Kind_T  := Normal_Execution)
      return V_Attributes
    with Post => not Make_Aux_Vertex_Attributes'Result.Is_Null_Node and
                 not Make_Aux_Vertex_Attributes'Result.Is_Program_Node;
   --  Create attributes for vertices modelling the following
   --  constructs:
   --
   --     * return statements without expression
   --     * when labels in a case statement
   --     * the faux exit for an infinite loop
   --
   --  No_Return flags this node as a dead end in the graph.

   function Make_Record_Tree_Attributes
     (Leaf : V_Attributes)
      return V_Attributes;
   --  Returns a copy of Leaf, but with blank def/use sets.

   function Make_Call_Attributes
     (Callsite   : Node_Id;
      Sub_Called : Node_Sets.Set     := Node_Sets.Empty_Set;
      Loops      : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc      : Node_Or_Entity_Id := Empty)
      return V_Attributes
   with Pre  => Nkind (Callsite) in N_Procedure_Call_Statement
                                  | N_Entry_Call_Statement,
        Post => not Make_Call_Attributes'Result.Is_Null_Node and
                Make_Call_Attributes'Result.Is_Program_Node and
                Make_Call_Attributes'Result.Is_Callsite;
   --  Create attributes for callsite vertices. Automatically sets the
   --  following:
   --     * Perform_IPFA
   --     * Is_Callsite

   function Make_Parameter_Attributes
     (FA                           : Flow_Analysis_Graphs;
      Call_Vertex                  : Node_Id;
      Actual                       : Node_Id;
      Formal                       : Entity_Id;
      In_Vertex                    : Boolean;
      Discriminants_Or_Bounds_Only : Boolean;
      Sub_Called                   : Node_Sets.Set := Node_Sets.Empty_Set;
      Loops                        : Node_Sets.Set;
      E_Loc                        : Node_Or_Entity_Id)
      return V_Attributes
   with Pre  => (if In_Vertex
                 then
                   Ekind (Formal) in E_In_Parameter | E_In_Out_Parameter
                     or else Discriminants_Or_Bounds_Only
                 else
                   Ekind (Formal) in E_Out_Parameter | E_In_Out_Parameter
                     and then not Discriminants_Or_Bounds_Only)
                and then Nkind (Actual) in N_Subexpr,
        Post =>
          not Make_Parameter_Attributes'Result.Is_Null_Node and
          not Make_Parameter_Attributes'Result.Is_Program_Node and
          not Make_Parameter_Attributes'Result.Is_Global_Parameter and
          Make_Parameter_Attributes'Result.Is_Parameter and
          Make_Parameter_Attributes'Result.Is_Discr_Or_Bounds_Parameter =
            Discriminants_Or_Bounds_Only;
   --  Create attributes for a parameter of a subprogram call. If In_Vertex is
   --  true, create attributes for the IN version of a parameter; otherwise,
   --  create attributes for the OUT version.
   --
   --  Note: variables defined and used are calculated automatically

   function Make_Global_Attributes
     (Call_Vertex                  : Node_Id;
      Global                       : Flow_Id;
      Scope                        : Flow_Scope;
      Discriminants_Or_Bounds_Only : Boolean;
      Loops                        : Node_Sets.Set;
      Is_Assertion                 : Boolean := False;
      E_Loc                        : Node_Or_Entity_Id := Empty)
      return V_Attributes
   with Pre  => (if Discriminants_Or_Bounds_Only
                 then Global.Variant = In_View
                 else Global.Variant in In_View | Out_View),
        Post => not Make_Global_Attributes'Result.Is_Null_Node and
                not Make_Global_Attributes'Result.Is_Program_Node and
                not Make_Global_Attributes'Result.Is_Parameter and
                Make_Global_Attributes'Result.Is_Global_Parameter;
   --  Create attributes for globals. Note that variables defined and
   --  used are calculated automatically.

   function Make_Implicit_Parameter_Attributes
     (Call_Vertex : Node_Id;
      Implicit    : Flow_Id;
      Scope       : Flow_Scope;
      Loops       : Node_Sets.Set;
      E_Loc       : Node_Or_Entity_Id)
      return V_Attributes
   with Post =>
     not Make_Implicit_Parameter_Attributes'Result.Is_Null_Node and
     not Make_Implicit_Parameter_Attributes'Result.Is_Program_Node and
     not Make_Implicit_Parameter_Attributes'Result.Is_Parameter and
     Make_Implicit_Parameter_Attributes'Result.Is_Implicit_Parameter;
   --  Creates the attributes for the implicit formal parameters of
   --  protected operations. Note that variables defined and used are
   --  calculated automatically.

   function Make_Null_Export_Attributes (F : Flow_Id) return V_Attributes;
   --  Creates the attributes for the synthetic null export.

   function Make_Variable_Attributes
     (F_Ent : Flow_Id;
      Mode  : Param_Mode;
      E_Loc : Node_Or_Entity_Id := Empty;
      S     : Flow_Scope := Null_Flow_Scope)
      return V_Attributes
   with Pre  => F_Ent.Kind in Direct_Mapping | Record_Field and
                F_Ent.Variant in Initial_Or_Final_Variant and
                Mode /= Mode_Proof and
                (if Present (S)
                 then F_Ent.Variant = Initial_Value and then
                   not Is_In_Analyzed_Files (Get_Direct_Mapping_Id (F_Ent))),
        Post => not Make_Variable_Attributes'Result.Is_Null_Node and
                not Make_Variable_Attributes'Result.Is_Program_Node and
                not Make_Variable_Attributes'Result.Is_Global;
   --  Create attributes for the initial_value and final_use
   --  vertices. We also calculate the following attributes
   --  automatically:
   --     * Is_Initialized
   --     * Is_Function_Return
   --     * Is_Global (always false)
   --     * Is_Loop_Parameter
   --     * Is_Export
   --     * Variables_Defined or Variables_Used
   --
   --  The scope parameter S is only set in phase 2 and only for constituents
   --  declared in private child packages; it is used to decide their
   --  initialization status.

   function Make_Global_Variable_Attributes
     (F    : Flow_Id;
      Mode : Param_Mode)
      return V_Attributes
   with Pre  => F.Variant in Initial_Or_Final_Variant,
        Post => not Make_Global_Variable_Attributes'Result.Is_Null_Node and
          not Make_Global_Variable_Attributes'Result.Is_Program_Node and
          Make_Global_Variable_Attributes'Result.Is_Global;
   --  Create attributes for the initial_value and final_use vertices
   --  for globals. The following is calculated automatically:
   --     * Is_Initialized
   --     * Is_Global (always true)
   --     * Is_Export
   --     * Variables_Defined or Variables_Used

   function Make_Default_Initialization_Attributes
     (FA    : Flow_Analysis_Graphs;
      Scope : Flow_Scope;
      F     : Flow_Id;
      Loops : Node_Sets.Set := Node_Sets.Empty_Set)
      return V_Attributes
   with Pre  => Is_Default_Initialized (F, Scope),
        Post =>
          not Make_Default_Initialization_Attributes'Result.Is_Null_Node
          and Make_Default_Initialization_Attributes'Result.Is_Default_Init;
   --  Create attributes for the default initialization vertices.

   function Make_Package_Initialization_Attributes
     (The_State : Flow_Id;
      Inputs    : Flow_Id_Sets.Set;
      Scope     : Flow_Scope;
      Loops     : Node_Sets.Set;
      E_Loc     : Node_Or_Entity_Id)
      return V_Attributes;
   --  Create attributes for package initialization vertices.

end Flow.Control_Flow_Graph.Utility;
