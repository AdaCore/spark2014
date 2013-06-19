------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--      F L O W . C O N T R O L _ F L O W _ G R A P H . U T I L I T Y       --
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

--  This package contains a few helper functions for CFG construction.

package Flow.Control_Flow_Graph.Utility is

   function Make_Basic_Attributes
     (Var_Def : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Var_Use : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Loops   : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc   : Node_Or_Entity_Id := Empty)
      return V_Attributes
      with Post => not Make_Basic_Attributes'Result.Is_Null_Node and
                   Make_Basic_Attributes'Result.Is_Program_Node;
   --  Create attributes for vertices which simply define and use some
   --  variables.

   function Make_Sink_Vertex_Attributes
     (Var_Use         : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Is_Precondition : Boolean           := False;
      Is_Loop_Entry   : Boolean           := False;
      E_Loc           : Node_Or_Entity_Id := Empty)
      return V_Attributes
      with Post => not Make_Sink_Vertex_Attributes'Result.Is_Null_Node and
                   not Make_Sink_Vertex_Attributes'Result.Is_Program_Node;
   --  Create attributes for vertices modelling the following
   --  constructs:
   --
   --     * pragmas

   function Make_Aux_Vertex_Attributes
     (E_Loc   : Node_Or_Entity_Id := Empty)
      return V_Attributes
      with Post => not Make_Aux_Vertex_Attributes'Result.Is_Null_Node and
                   not Make_Aux_Vertex_Attributes'Result.Is_Program_Node;
   --  Create attributes for vertices modelling the following
   --  constructs:
   --
   --     * return statements without expression
   --     * when labels in a case statement

   function Make_Record_Tree_Attributes
     (Leaf : V_Attributes)
      return V_Attributes;
   --  Returns a copy of Leaf, but with blank def/use sets.

   function Make_Call_Attributes
     (Callsite     : Node_Id           := Empty;
      Refined_View : Boolean           := False;
      Loops        : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc        : Node_Or_Entity_Id := Empty)
      return V_Attributes
      with Pre  => Present (Callsite),
           Post => not Make_Call_Attributes'Result.Is_Null_Node and
                   Make_Call_Attributes'Result.Is_Program_Node and
                   Make_Call_Attributes'Result.Is_Callsite and
                   Make_Call_Attributes'Result.Use_Refined_View = Refined_View;
   --  Create attributes for callsite vertices. Automatically sets the
   --  following:
   --     * Perform_IPFA
   --     * Is_Callsite

   function Make_Parameter_Attributes
     (Call_Vertex        : Node_Id;
      Actual             : Node_Id;
      Formal             : Node_Id;
      In_Vertex          : Boolean;
      Discriminants_Only : Boolean;
      Loops              : Node_Sets.Set;
      E_Loc              : Node_Or_Entity_Id := Empty)
      return V_Attributes
      with Pre  => (if Discriminants_Only then In_Vertex),
           Post =>
             not Make_Parameter_Attributes'Result.Is_Null_Node and
             not Make_Parameter_Attributes'Result.Is_Program_Node and
             not Make_Parameter_Attributes'Result.Is_Global_Parameter and
             Make_Parameter_Attributes'Result.Is_Parameter and
             Make_Parameter_Attributes'Result.Is_Discriminants_Only_Parameter =
               Discriminants_Only;
   --  Create attributes for parameters for subprogram calls. If
   --  In_Vertex is true, create the attributes for the in version of
   --  a parameter; if In_Vertex is false we create the attributes for
   --  the out version. Note that variables defined and used is
   --  calculated automatically.

   function Make_Global_Attributes
     (Call_Vertex        : Node_Id;
      Global             : Flow_Id;
      Discriminants_Only : Boolean;
      Loops              : Node_Sets.Set;
      E_Loc              : Node_Or_Entity_Id := Empty)
      return V_Attributes
      with Pre  => (if Discriminants_Only then Global.Variant = In_View),
           Post => not Make_Global_Attributes'Result.Is_Null_Node and
                   not Make_Global_Attributes'Result.Is_Program_Node and
                   not Make_Global_Attributes'Result.Is_Parameter and
                   Make_Global_Attributes'Result.Is_Global_Parameter;
   --  Create attributes for globals. Note that variables defined and
   --  used is calculated automatically.

   function Make_Variable_Attributes
     (F_Ent : Flow_Id;
      E_Loc : Node_Or_Entity_Id := Empty)
      return V_Attributes
      with Pre  => F_Ent.Kind in Direct_Mapping | Record_Field,
           Post => not Make_Variable_Attributes'Result.Is_Null_Node and
                   not Make_Variable_Attributes'Result.Is_Program_Node and
                   not Make_Variable_Attributes'Result.Is_Global;
   --  Create attributes for the initial_value and final_use
   --  vertices. We also calculate the following attributes
   --  automatically:
   --     * Is_Initialised
   --     * Is_Function_Return
   --     * Is_Global (always false)
   --     * Is_Loop_Parameter
   --     * Is_Export
   --     * Variables_Defined or Variables_Used

   function Make_Global_Variable_Attributes
     (F       : Flow_Id;
      Mode    : Global_Modes;
      E_Loc   : Node_Or_Entity_Id := Empty)
      return V_Attributes
      with Pre  => F.Variant in Initial_Or_Final_Variant,
           Post => not Make_Global_Variable_Attributes'Result.Is_Null_Node and
             not Make_Global_Variable_Attributes'Result.Is_Program_Node and
             Make_Global_Variable_Attributes'Result.Is_Global;

   --  Create attributes for the initial_value and final_use vertices
   --  for globals. The following is calculated automatically:
   --     * Is_Initialised
   --     * Is_Global (always true)
   --     * Is_Export
   --     * Variables_Defined or Variables_Used

   function Make_Default_Initialization_Attributes
     (F       : Flow_Id;
      Loops   : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc   : Node_Or_Entity_Id := Empty)
      return V_Attributes
      with Post =>
        not Make_Default_Initialization_Attributes'Result.Is_Null_Node and
        Make_Default_Initialization_Attributes'Result.Is_Default_Init;
   --  Create attributes for the default initialization vertices.

end Flow.Control_Flow_Graph.Utility;
