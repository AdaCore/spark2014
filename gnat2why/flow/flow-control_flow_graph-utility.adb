------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--      F L O W . C O N T R O L _ F L O W _ G R A P H . U T I L I T Y       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2014, Altran UK Limited              --
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

with Flow_Tree_Utility; use Flow_Tree_Utility;
with Flow_Utility;      use Flow_Utility;

package body Flow.Control_Flow_Graph.Utility is

   use type Flow_Id_Sets.Set;

   procedure Add_Volatile_Effects
     (A      : in out V_Attributes;
      Global : Flow_Id := Null_Flow_Id);
   --  This helper procedure inspects the variables used by a particular
   --  vertex. Any with a volatile property causing reads or writes to be
   --  effective will be noted in the volatiles_read and volatiles_written
   --  sets (as appropriate).
   --
   --  When Global is Present, specifically add its volatile effects.
   --  This is used to add the effects of external abstract states and
   --  is only ever called from Make_Global_Attributes.
   --
   --  This procedure should not be blindly called in all cases; in
   --  particular for 'inital and 'final vertices it should not be used.

   --------------------------
   -- Add_Volatile_Effects --
   --------------------------

   procedure Add_Volatile_Effects
     (A      : in out V_Attributes;
      Global : Flow_Id := Null_Flow_Id)
   is
   begin
      if Present (Global) then
         if Has_Effective_Reads (Global) then
            A.Volatiles_Read.Include (Global);
         end if;
         if Has_Effective_Writes (Global) then
            A.Volatiles_Written.Include (Global);
         end if;
      end if;

      for F of A.Variables_Explicitly_Used loop
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
     (Var_Def    : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Var_Ex_Use : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Var_Im_Use : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Loops      : Node_Sets.Set       := Node_Sets.Empty_Set;
      E_Loc      : Node_Or_Entity_Id   := Empty;
      Print_Hint : Pretty_Print_Kind_T := Pretty_Print_Null)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Is_Program_Node           := True;
      A.Variables_Defined         := Var_Def;
      A.Variables_Used            := Var_Ex_Use or Var_Im_Use;
      A.Variables_Explicitly_Used := Var_Ex_Use;
      A.Loops                     := Loops;
      A.Error_Location            := E_Loc;
      A.Pretty_Print_Kind         := Print_Hint;

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
      A.Is_Program_Node           := True;
      A.Variables_Defined         := Var_Def;
      A.Variables_Used            := Var_Use;
      A.Variables_Explicitly_Used := Var_Use;
      A.Loops                     := Loops;
      A.Error_Location            := E_Loc;
      A.Aux_Node                  := Object_Returned;

      Add_Volatile_Effects (A);
      return A;
   end Make_Extended_Return_Attributes;

   ---------------------------------
   -- Make_Sink_Vertex_Attributes --
   ---------------------------------

   function Make_Sink_Vertex_Attributes
     (Var_Use          : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Is_Precondition  : Boolean           := False;
      Is_Postcondition : Boolean           := False;
      Is_Loop_Entry    : Boolean           := False;
      Is_Fold_Check    : Boolean           := False;
      E_Loc            : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Variables_Used            := Var_Use;
      A.Variables_Explicitly_Used := Var_Use;
      A.Is_Precondition           := Is_Precondition;
      A.Is_Postcondition          := Is_Postcondition;
      A.Is_Loop_Entry             := Is_Loop_Entry;
      A.Error_Location            := E_Loc;

      if Is_Fold_Check then
         A.Pretty_Print_Kind := Pretty_Print_Folded_Function_Check;
      end if;

      Add_Volatile_Effects (A);
      return A;
   end Make_Sink_Vertex_Attributes;

   --------------------------------
   -- Make_Aux_Vertex_Attributes --
   --------------------------------

   function Make_Aux_Vertex_Attributes
     (E_Loc     : Node_Or_Entity_Id := Empty;
      Execution : Execution_Kind_T  := Normal_Execution)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Error_Location := E_Loc;
      A.Execution      := Execution;

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
      A.Variables_Used            := Flow_Id_Sets.Empty_Set;
      A.Variables_Explicitly_Used := Flow_Id_Sets.Empty_Set;
      A.Variables_Defined         := Flow_Id_Sets.Empty_Set;

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
     (FA                           : Flow_Analysis_Graphs;
      Call_Vertex                  : Node_Id;
      Actual                       : Node_Id;
      Formal                       : Node_Id;
      In_Vertex                    : Boolean;
      Discriminants_Or_Bounds_Only : Boolean;
      Loops                        : Node_Sets.Set;
      E_Loc                        : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A        : V_Attributes        := Null_Attributes;
      Tmp_Used : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Scope    : constant Flow_Scope := Get_Flow_Scope (Call_Vertex);
      Unused   : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
   begin
      A.Is_Parameter                  := True;
      A.Is_Discr_Or_Bounds_Parameter  := Discriminants_Or_Bounds_Only;
      A.Call_Vertex      := Direct_Mapping_Id (Call_Vertex);
      A.Parameter_Actual := Direct_Mapping_Id (Actual);
      A.Parameter_Formal := Direct_Mapping_Id (Formal);
      A.Loops            := Loops;
      A.Error_Location   := E_Loc;

      if In_Vertex then
         pragma Assert
           (Ekind (Formal) in E_In_Parameter | E_In_Out_Parameter or else
              Discriminants_Or_Bounds_Only);

         Tmp_Used := Get_Variable_Set (Actual,
                                       Scope           => Scope,
                                       Local_Constants => FA.Local_Constants,
                                       Fold_Functions  => True);
         for F of Tmp_Used loop
            if (if Discriminants_Or_Bounds_Only
                then Is_Discriminant (F))
            then
               A.Variables_Used.Include (F);
               A.Variables_Explicitly_Used.Include (F);
            end if;
            if not Is_Bound (F) and then Has_Bounds (F) then
               A.Variables_Used.Include
                 (F'Update (Bound => (Kind => Some_Bound)));
               A.Variables_Explicitly_Used.Include
                 (F'Update (Bound => (Kind => Some_Bound)));
            end if;
         end loop;
      else
         pragma Assert
           (Ekind (Formal) in E_Out_Parameter | E_In_Out_Parameter);
         pragma Assert (not Discriminants_Or_Bounds_Only);
         Untangle_Assignment_Target
           (N                    => Actual,
            Scope                => Scope,
            Local_Constants      => FA.Local_Constants,
            Vars_Explicitly_Used => A.Variables_Explicitly_Used,
            Vars_Implicitly_Used => A.Variables_Used,
            Vars_Defined         => A.Variables_Defined,
            Vars_Semi_Used       => Unused);
         --  We can ignore Vars_Semi_Used here as we have an unconditional
         --  addition to folded_function_checks for each actual anyway.
         A.Variables_Used.Union (A.Variables_Explicitly_Used);
      end if;

      Add_Volatile_Effects (A);
      return A;
   end Make_Parameter_Attributes;

   ----------------------------
   -- Make_Global_Attributes --
   ----------------------------

   function Make_Global_Attributes
     (Call_Vertex                  : Node_Id;
      Global                       : Flow_Id;
      Discriminants_Or_Bounds_Only : Boolean;
      Loops                        : Node_Sets.Set;
      E_Loc                        : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Is_Global_Parameter             := True;
      A.Is_Discr_Or_Bounds_Parameter    := Discriminants_Or_Bounds_Only;
      A.Call_Vertex         := Direct_Mapping_Id (Call_Vertex);
      A.Parameter_Formal    := Global;
      A.Loops               := Loops;
      A.Error_Location      := E_Loc;

      case Global.Variant is
         when In_View =>
            for F of Flatten_Variable
              (Change_Variant (Global, Normal_Use))
            loop
               if not Discriminants_Or_Bounds_Only or else
                 Is_Discriminant (F)
               then
                  A.Variables_Used.Include (F);
                  A.Variables_Explicitly_Used.Include (F);
               end if;

               if not Is_Bound (F) and then Has_Bounds (F) then
                  A.Variables_Used.Include
                    (F'Update (Bound => (Kind => Some_Bound)));
                  A.Variables_Explicitly_Used.Include
                    (F'Update (Bound => (Kind => Some_Bound)));
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

      Add_Volatile_Effects (A, Global);
      return A;
   end Make_Global_Attributes;

   ---------------------------------
   -- Make_Null_Export_Attributes --
   ---------------------------------

   function Make_Null_Export_Attributes (F : Flow_Id) return V_Attributes is
      A : V_Attributes := Null_Attributes;
   begin
      case F.Variant is
         when Initial_Value =>
            A.Variables_Defined :=
              Flow_Id_Sets.To_Set (Change_Variant (F, Normal_Use));

         when Final_Value =>
            A.Variables_Used :=
              Flow_Id_Sets.To_Set (Change_Variant (F, Normal_Use));

            A.Variables_Explicitly_Used := A.Variables_Used;

            A.Is_Export := True;

         when others =>
            raise Program_Error;
      end case;

      return A;
   end Make_Null_Export_Attributes;

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

            if Is_Discriminant (F_Ent) or Is_Bound (F_Ent) then
               --  Discriminants and array bounds are *always* initialized.
               --  They are also implicit imports if they are out
               --  parameters.
               A.Is_Initialized := True;
               if Ekind (Entire_Var) = E_Out_Parameter then
                  A.Is_Import := True;
               end if;
            end if;

            if Has_Async_Writers (F_Ent) then
               --  SRM 7.1.2(14) states that objects with async_writers are
               --  always considered to be initialized.
               A.Is_Initialized := True;
            end if;

            A.Is_Loop_Parameter := Ekind (Entire_Var) = E_Loop_Parameter;

            A.Variables_Defined := Flow_Id_Sets.To_Set (Change_Variant
                                                          (F_Ent, Normal_Use));

         when Final_Value =>
            A.Is_Export := Ekind (Entire_Var) in
              E_In_Out_Parameter |
                 E_Out_Parameter |
                 E_Function;

            if Is_Bound (F_Ent) then
               --  Array bounds are not exported.
               A.Is_Export := False;
            end if;

            A.Is_Loop_Parameter := Ekind (Entire_Var) = E_Loop_Parameter;

            A.Variables_Used := Flow_Id_Sets.To_Set (Change_Variant
                                                       (F_Ent, Normal_Use));
            A.Variables_Explicitly_Used := A.Variables_Used;

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

            if Is_Discriminant (F) or Is_Bound (F) then
               --  Discriminants or array bounds are *always* initialized
               --  imports.
               A.Is_Initialized := True;
               A.Is_Import      := True;
            end if;

            A.Is_Import         := A.Is_Initialized;
            A.Variables_Defined :=
              Flow_Id_Sets.To_Set (Change_Variant (F, Normal_Use));

         when Final_Value =>
            A.Is_Export      := Mode in Exported_Global_Modes;

            if Is_Bound (F) then
               --  Array bounds are not exported.
               A.Is_Export := False;
            end if;

            A.Variables_Used :=
              Flow_Id_Sets.To_Set (Change_Variant (F, Normal_Use));
            A.Variables_Explicitly_Used := A.Variables_Used;

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
            Local_Constants => FA.Local_Constants,
            Fold_Functions  => False);
         A.Variables_Explicitly_Used := A.Variables_Used;
      end if;

      Add_Volatile_Effects (A);
      return A;
   end Make_Default_Initialization_Attributes;

end Flow.Control_Flow_Graph.Utility;
