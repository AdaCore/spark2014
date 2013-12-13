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

with Sinfo;             use Sinfo;

with Why;

with Flow.Utility;      use Flow.Utility;
with Flow_Tree_Utility; use Flow_Tree_Utility;

package body Flow.Control_Flow_Graph.Utility is

   procedure Add_Volatile_Effects (A : in out V_Attributes);
   --  This helper procedure inspects the variables used by a particular
   --  vertex. Any with a volatile property causing reads or writes to be
   --  effective will be noted in the volatiles_read and volatiles_written
   --  sets (as appropriate).
   --
   --  This procedure should not be blindly called in all cases; in
   --  particular for 'inital and 'final vertices it should not be used.

   -------------------------
   -- Add_Volatile_Effets --
   -------------------------

   procedure Add_Volatile_Effects (A : in out V_Attributes) is
   begin
      for F of A.Variables_Used loop
         if Has_Effective_Reads (F) then
            A.Volatiles_Read.Include (F);
         end if;
      end loop;
      for F of A.Variables_Defined loop
         if Has_Effective_Writes (F) then
            A.Volatiles_Written.Include (F);
         end if;
      end loop;
   end Add_Volatile_Effects;

   ---------------------------
   -- Make_Basic_Attributes --
   ---------------------------

   function Make_Basic_Attributes
     (Var_Def  : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Var_Use  : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Loops    : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc    : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Is_Program_Node   := True;
      A.Variables_Defined := Var_Def;
      A.Variables_Used    := Var_Use;
      A.Loops             := Loops;
      A.Error_Location    := E_Loc;

      Add_Volatile_Effects (A);
      return A;
   end Make_Basic_Attributes;

   ------------------------------------
   -- Make_Extened_Return_Attributes --
   ------------------------------------

   function Make_Extended_Return_Attributes
     (Var_Def         : Flow_Id_Sets.Set;
      Var_Use         : Flow_Id_Sets.Set;
      Object_Returned : Entity_Id;
      Loops           : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc           : Node_Or_Entity_Id := Empty)
     return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Is_Program_Node   := True;
      A.Variables_Defined := Var_Def;
      A.Variables_Used    := Var_Use;
      A.Loops             := Loops;
      A.Error_Location    := E_Loc;
      A.Aux_Node          := Object_Returned;

      Add_Volatile_Effects (A);
      return A;
   end Make_Extended_Return_Attributes;

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

      Add_Volatile_Effects (A);
      --  ??? volatility correct here?
      return A;
   end Make_Sink_Vertex_Attributes;

   --------------------------------
   -- Make_Aux_Vertex_Attributes --
   --------------------------------

   function Make_Aux_Vertex_Attributes
     (E_Loc     : Node_Or_Entity_Id := Empty;
      No_Return : Boolean           := False)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Error_Location      := E_Loc;
      A.No_Return_From_Here := No_Return;

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
      A.Error_Location   := E_Loc;

      --  ??? The below is the logic for doing IPFA within a
      --  compilation unit. To be enabled by M227-027.
      --
      --  Make sure that once this is implemented, the mechanism for analysing
      --  single subprograms is not broken.

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
     (FA                 : Flow_Analysis_Graphs;
      Call_Vertex        : Node_Id;
      Actual             : Node_Id;
      Formal             : Node_Id;
      In_Vertex          : Boolean;
      Discriminants_Only : Boolean;
      Loops              : Node_Sets.Set;
      E_Loc              : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A        : V_Attributes        := Null_Attributes;
      Tmp_Used : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Scope    : constant Flow_Scope := Get_Flow_Scope (Call_Vertex);
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

         Tmp_Used := Get_Variable_Set (Actual,
                                       Scope           => Scope,
                                       Local_Constants => FA.Local_Constants);
         for F of Tmp_Used loop
            if not Discriminants_Only or else Is_Discriminant (F) then
               A.Variables_Used.Include (F);
            end if;
         end loop;
      else
         pragma Assert
           (Ekind (Formal) in E_Out_Parameter | E_In_Out_Parameter);
         pragma Assert (not Discriminants_Only);
         Untangle_Assignment_Target (N               => Actual,
                                     Scope           => Scope,
                                     Local_Constants => FA.Local_Constants,
                                     Vars_Defined    => A.Variables_Defined,
                                     Vars_Used       => A.Variables_Used);
      end if;

      Add_Volatile_Effects (A);
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

      Add_Volatile_Effects (A);
      return A;
   end Make_Global_Attributes;

   ------------------------------
   -- Make_Variable_Attributes --
   ------------------------------

   function Make_Variable_Attributes
     (F_Ent : Flow_Id;
      Mode  : Param_Mode;
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
      A.Mode               := Mode;

      case F_Ent.Variant is
         when Initial_Value =>
            A.Is_Initialized := Ekind (Entire_Var) in
              E_In_Out_Parameter |
                 E_In_Parameter  |
                 E_Loop_Parameter;

            A.Is_Import := Ekind (Entire_Var) in
              E_In_Out_Parameter | E_In_Parameter;

            if Is_Discriminant (F_Ent) then
               --  Discriminants are *always* initialized. They are also
               --  implicit imports if they are out parameters.
               A.Is_Initialized := True;
               if Ekind (Entire_Var) = E_Out_Parameter then
                  A.Is_Import := True;
               end if;
            end if;

            A.Is_Loop_Parameter := Ekind (Entire_Var) = E_Loop_Parameter;

            A.Variables_Defined := Flow_Id_Sets.To_Set (Change_Variant
                                                          (F_Ent, Normal_Use));

         when Final_Value =>
            A.Is_Export := Ekind (Entire_Var) in
              E_In_Out_Parameter |
                 E_Out_Parameter |
                 E_Function;

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
      Mode    : Param_Mode;
      Uninit  : Boolean           := False;
      E_Loc   : Node_Or_Entity_Id := Empty)
      return V_Attributes is
      A : V_Attributes := Null_Attributes;
   begin
      A.Error_Location := E_Loc;
      A.Is_Global      := True;
      A.Is_Constant    := Mode in In_Global_Modes;
      A.Mode           := Mode;

      case F.Variant is
         when Initial_Value =>
            A.Is_Initialized    := (not Uninit) and
              Mode in Initialized_Global_Modes;

            if Is_Discriminant (F) then
               --  Discriminants are *always* initialized imports.
               A.Is_Initialized := True;
               A.Is_Import      := True;
            end if;

            A.Is_Import         := A.Is_Initialized;
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
     (FA      : Flow_Analysis_Graphs;
      Scope   : Flow_Scope;
      F       : Flow_Id;
      Loops   : Node_Sets.Set := Node_Sets.Empty_Set)
      return V_Attributes
   is
      A  : V_Attributes     := Null_Attributes;
      DI : constant Node_Id := Get_Default_Initialization (F);
   begin
      A.Is_Default_Init   := True;
      A.Loops             := Loops;
      if Present (DI) then
         A.Error_Location := DI;
      else
         A.Error_Location := Etype (Get_Direct_Mapping_Id (F));
      end if;

      A.Default_Init_Var := F;
      A.Default_Init_Val := DI;

      A.Variables_Defined := Flow_Id_Sets.To_Set (F);
      if Present (DI) then
         A.Variables_Used := Get_Variable_Set
           (A.Default_Init_Val,
            Scope           => Scope,
            Local_Constants => FA.Local_Constants);
      end if;

      Add_Volatile_Effects (A);
      return A;
   end Make_Default_Initialization_Attributes;

end Flow.Control_Flow_Graph.Utility;
