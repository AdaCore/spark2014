------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--      F L O W . C O N T R O L _ F L O W _ G R A P H . U T I L I T Y       --
--                                                                          --
--                                 B o d y                                  --
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

with Sinfo; use Sinfo;

with Why;

with Flow.Utility; use Flow.Utility;

package body Flow.Control_Flow_Graph.Utility is

   ---------------------------
   -- Make_Basic_Attributes --
   ---------------------------

   function Make_Basic_Attributes
     (Var_Def  : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Var_Use  : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Loops    : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc    : Node_Or_Entity_Id := Empty;
      Aux_Node : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Is_Program_Node   := True;
      A.Variables_Defined := Var_Def;
      A.Variables_Used    := Var_Use;
      A.Loops             := Loops;
      A.Error_Location    := E_Loc;
      A.Aux_Node          := Aux_Node;

      return A;
   end Make_Basic_Attributes;

   ---------------------------------
   -- Make_Sink_Vertex_Attributes --
   ---------------------------------

   function Make_Sink_Vertex_Attributes
     (Var_Use         : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Is_Precondition : Boolean           := False;
      Is_Loop_Entry   : Boolean           := False;
      E_Loc           : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Variables_Used  := Var_Use;
      A.Is_Precondition := Is_Precondition;
      A.Is_Loop_Entry   := Is_Loop_Entry;
      A.Error_Location  := E_Loc;

      return A;
   end Make_Sink_Vertex_Attributes;

   --------------------------------
   -- Make_Aux_Vertex_Attributes --
   --------------------------------

   function Make_Aux_Vertex_Attributes
     (E_Loc   : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Error_Location := E_Loc;

      return A;
   end Make_Aux_Vertex_Attributes;

   ---------------------------------
   -- Make_Record_Tree_Attributes --
   ---------------------------------

   function Make_Record_Tree_Attributes (Leaf : V_Attributes)
                                         return V_Attributes
   is
      A : V_Attributes := Leaf;
   begin
      A.Variables_Used    := Flow_Id_Sets.Empty_Set;
      A.Variables_Defined := Flow_Id_Sets.Empty_Set;

      return A;
   end Make_Record_Tree_Attributes;

   --------------------------
   -- Make_Call_Attributes --
   --------------------------

   function Make_Call_Attributes
     (Callsite     : Node_Id           := Empty;
      Refined_View : Boolean           := False;
      Loops        : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc        : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;

      Called_Procedure : constant Entity_Id := Entity (Name (Callsite));
      Procedure_Spec   : constant Node_Id   :=
        Get_Procedure_Specification (Called_Procedure);
   begin
      pragma Assert (Nkind (Procedure_Spec) = N_Procedure_Specification);

      A.Is_Program_Node  := True;
      A.Loops            := Loops;
      A.Is_Callsite      := True;
      A.Use_Refined_View := Refined_View;
      A.Error_Location   := E_Loc;

      --  ??? The below is the logic for doing IPFA within a
      --  compilation unit. To be enabled by M227-027.

      --  case Nkind (Parent (Procedure_Spec)) is
      --     when N_Subprogram_Body =>
      --        A.Perform_IPFA := True;
      --     when N_Subprogram_Declaration =>
      --        A.Perform_IPFA :=
      --          Present (Corresponding_Body (Parent (Procedure_Spec)));
      --     when others =>
      --        Print_Node_Subtree (Parent (Procedure_Spec));
      --        raise Why.Unexpected_Node;
      --  end case;

      return A;
   end Make_Call_Attributes;

   -------------------------------
   -- Make_Parameter_Attributes --
   -------------------------------

   function Make_Parameter_Attributes
     (Call_Vertex        : Node_Id;
      Actual             : Node_Id;
      Formal             : Node_Id;
      In_Vertex          : Boolean;
      Discriminants_Only : Boolean;
      Loops              : Node_Sets.Set;
      E_Loc              : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A        : V_Attributes       := Null_Attributes;
      Tmp_Used : Flow_Id_Sets.Set   := Flow_Id_Sets.Empty_Set;
      Scope    : constant Scope_Ptr := Get_Enclosing_Body_Scope (Call_Vertex);
   begin
      A.Is_Parameter                    := True;
      A.Is_Discriminants_Only_Parameter := Discriminants_Only;
      A.Call_Vertex      := Direct_Mapping_Id (Call_Vertex);
      A.Parameter_Actual := Direct_Mapping_Id (Actual);
      A.Parameter_Formal := Direct_Mapping_Id (Formal);
      A.Loops            := Loops;
      A.Error_Location   := E_Loc;

      if In_Vertex then
         pragma Assert
           (Ekind (Formal) in E_In_Parameter | E_In_Out_Parameter or else
              Discriminants_Only);

         Tmp_Used := Get_Variable_Set (Scope, Actual);
         for F of Tmp_Used loop
            if not Discriminants_Only or else Is_Discriminant (F) then
               A.Variables_Used.Include (F);
            end if;
         end loop;
      else
         pragma Assert
           (Ekind (Formal) in E_Out_Parameter | E_In_Out_Parameter);
         pragma Assert (not Discriminants_Only);
         Untangle_Assignment_Target (Scope        => Scope,
                                     N            => Actual,
                                     Vars_Defined => A.Variables_Defined,
                                     Vars_Used    => A.Variables_Used);
      end if;

      return A;
   end Make_Parameter_Attributes;

   ----------------------------
   -- Make_Global_Attributes --
   ----------------------------

   function Make_Global_Attributes
     (Call_Vertex        : Node_Id;
      Global             : Flow_Id;
      Discriminants_Only : Boolean;
      Loops              : Node_Sets.Set;
      E_Loc              : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Is_Global_Parameter             := True;
      A.Is_Discriminants_Only_Parameter := Discriminants_Only;
      A.Call_Vertex         := Direct_Mapping_Id (Call_Vertex);
      A.Parameter_Formal    := Global;
      A.Loops               := Loops;
      A.Error_Location      := E_Loc;

      case Global.Variant is
         when In_View =>
            for F of Flatten_Variable
              (Change_Variant (Global, Normal_Use))
            loop
               if not Discriminants_Only or else Is_Discriminant (F) then
                  A.Variables_Used.Include (F);
               end if;
            end loop;

         when Out_View =>
            --  We do not need untangle_assignment_target as we only
            --  ever update the entire global.
            A.Variables_Defined := Flatten_Variable
              (Change_Variant (Global, Normal_Use));

         when others =>
            raise Program_Error;
      end case;

      return A;
   end Make_Global_Attributes;

   ------------------------------
   -- Make_Variable_Attributes --
   ------------------------------

   function Make_Variable_Attributes
     (F_Ent : Flow_Id;
      E_Loc : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A          : V_Attributes       := Null_Attributes;
      Entire_Var : constant Entity_Id := F_Ent.Node;
   begin
      A.Error_Location     := E_Loc;
      A.Is_Constant        :=
        Ekind (Entire_Var) in E_In_Parameter | E_Loop_Parameter;
      A.Is_Function_Return := Ekind (Entire_Var) = E_Function;
      A.Is_Package_State   := Is_Package_State (Entire_Var);

      case F_Ent.Variant is
         when Initial_Value =>
            A.Is_Initialised := Ekind (Entire_Var) in
              E_In_Out_Parameter |
                 E_In_Parameter  |
                 E_Loop_Parameter;

            A.Is_Import := Ekind (Entire_Var) in
              E_In_Out_Parameter | E_In_Parameter;

            if Is_Discriminant (F_Ent) then
               --  Discriminants are *always* initialized imports.
               A.Is_Initialised := True;
               A.Is_Import      := True;
            end if;

            A.Is_Loop_Parameter := Ekind (Entire_Var) = E_Loop_Parameter;

            A.Variables_Defined := Flow_Id_Sets.To_Set (Change_Variant
                                                          (F_Ent, Normal_Use));

         when Final_Value =>
            A.Is_Export := Ekind (Entire_Var) in
              E_In_Out_Parameter |
                 E_Out_Parameter |
                 E_Function
              or Is_Initialized_At_Elaboration (Entire_Var);

            A.Is_Loop_Parameter := Ekind (Entire_Var) = E_Loop_Parameter;

            A.Variables_Used := Flow_Id_Sets.To_Set (Change_Variant
                                                       (F_Ent, Normal_Use));

         when others =>
            raise Why.Unexpected_Node;
      end case;

      return A;
   end Make_Variable_Attributes;

   -------------------------------------
   -- Make_Global_Variable_Attributes --
   -------------------------------------

   function Make_Global_Variable_Attributes
     (F       : Flow_Id;
      Mode    : Global_Modes;
      E_Loc   : Node_Or_Entity_Id := Empty)
      return V_Attributes is
      A : V_Attributes := Null_Attributes;
   begin
      A.Error_Location := E_Loc;
      A.Is_Global      := True;
      A.Is_Constant    := Mode in In_Global_Modes;

      case F.Variant is
         when Initial_Value =>
            A.Is_Initialised    := Mode in Initialised_Global_Modes;

            if Is_Discriminant (F) then
               --  Discriminants are *always* initialized imports.
               A.Is_Initialised := True;
               A.Is_Import      := True;
            end if;

            A.Is_Import         := A.Is_Initialised;
            A.Variables_Defined :=
              Flow_Id_Sets.To_Set (Change_Variant (F, Normal_Use));

         when Final_Value =>
            A.Is_Export      := Mode in Exported_Global_Modes;
            A.Variables_Used :=
              Flow_Id_Sets.To_Set (Change_Variant (F, Normal_Use));

         when others =>
            raise Program_Error;
      end case;

      return A;
   end Make_Global_Variable_Attributes;

   --------------------------------------------
   -- Make_Default_Initialization_Attributes --
   --------------------------------------------

   function Make_Default_Initialization_Attributes
     (Scope   : Scope_Ptr;
      F       : Flow_Id;
      Loops   : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc   : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Is_Default_Init   := True;
      A.Loops             := Loops;
      A.Error_Location    := E_Loc;

      A.Default_Init_Var  := F;
      A.Default_Init_Val  := Get_Default_Initialization (F);

      A.Variables_Defined := Flow_Id_Sets.To_Set (F);
      A.Variables_Used    := Get_Variable_Set (Scope, A.Default_Init_Val);

      return A;
   end Make_Default_Initialization_Attributes;

end Flow.Control_Flow_Graph.Utility;
