------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--      F L O W . C O N T R O L _ F L O W _ G R A P H . U T I L I T Y       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2017, Altran UK Limited              --
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

with Flow_Utility;                  use Flow_Utility;
with Sem_Type;                      use Sem_Type;
with Sinfo;                         use Sinfo;
with SPARK_Util.Subprograms;        use SPARK_Util.Subprograms;

package body Flow.Control_Flow_Graph.Utility is

   use type Flow_Id_Sets.Set;

   procedure Add_Volatile_Effects
     (A      : in out V_Attributes;
      Global : Flow_Id    := Null_Flow_Id);
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

   function Refers_To_Ghost
     (FA  : Flow_Analysis_Graphs;
      Atr : V_Attributes)
      return Boolean;
   --  Checks if Atr refers to a Ghost. This function is mainly used
   --  to set the Is_Proof field of V_Attributes.

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
     (FA         : Flow_Analysis_Graphs;
      Var_Def    : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Var_Ex_Use : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Var_Im_Use : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Sub_Called : Node_Sets.Set       := Node_Sets.Empty_Set;
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
      A.Subprograms_Called        := Sub_Called;
      A.Loops                     := Loops;
      A.Error_Location            := E_Loc;
      A.Pretty_Print_Kind         := Print_Hint;
      A.Is_Proof                  := Refers_To_Ghost (FA, A);

      Add_Volatile_Effects (A);
      return A;
   end Make_Basic_Attributes;

   ------------------------------------
   -- Make_Extened_Return_Attributes --
   ------------------------------------

   function Make_Extended_Return_Attributes
     (FA              : Flow_Analysis_Graphs;
      Var_Def         : Flow_Id_Sets.Set;
      Var_Use         : Flow_Id_Sets.Set;
      Object_Returned : Entity_Id;
      Sub_Called      : Node_Sets.Set     := Node_Sets.Empty_Set;
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
      A.Subprograms_Called        := Sub_Called;
      A.Loops                     := Loops;
      A.Error_Location            := E_Loc;
      A.Aux_Node                  := Object_Returned;
      A.Is_Proof                  := Refers_To_Ghost (FA, A);

      Add_Volatile_Effects (A);
      return A;
   end Make_Extended_Return_Attributes;

   ---------------------------------
   -- Make_Sink_Vertex_Attributes --
   ---------------------------------

   function Make_Sink_Vertex_Attributes
     (FA               : Flow_Analysis_Graphs;
      Var_Use          : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Sub_Called       : Node_Sets.Set     := Node_Sets.Empty_Set;
      Is_Proof         : Boolean           := False;
      Is_DIC           : Boolean           := False;
      Is_Precondition  : Boolean           := False;
      Is_Postcondition : Boolean           := False;
      Is_Loop_Entry    : Boolean           := False;
      Is_Fold_Check    : Boolean           := False;
      E_Loc            : Node_Or_Entity_Id := Empty;
      Execution        : Execution_Kind_T  := Normal_Execution)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Variables_Used            := Var_Use;
      A.Variables_Explicitly_Used := Var_Use;
      A.Subprograms_Called        := Sub_Called;
      A.Is_Proof                  := Is_Proof or else Refers_To_Ghost (FA, A);
      A.Is_Precondition           := Is_Precondition;
      A.Is_Postcondition          := Is_Postcondition;
      A.Is_Loop_Entry             := Is_Loop_Entry;
      A.Error_Location            := E_Loc;
      A.Execution                 := Execution;

      if Is_Fold_Check then
         A.Pretty_Print_Kind := Pretty_Print_Folded_Function_Check;
      elsif Is_DIC then
         A.Pretty_Print_Kind := Pretty_Print_DIC;
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
     (FA         : Flow_Analysis_Graphs;
      Callsite   : Node_Id           := Empty;
      Sub_Called : Node_Sets.Set     := Node_Sets.Empty_Set;
      Loops      : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc      : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
      pragma Unreferenced (Callsite);
   begin
      A.Subprograms_Called := Sub_Called;
      A.Is_Program_Node    := True;
      A.Loops              := Loops;
      A.Is_Callsite        := True;
      A.Error_Location     := E_Loc;
      A.Is_Proof           := Refers_To_Ghost (FA, A);

      --  ??? The below is the logic for doing IPFA within a
      --  compilation unit. To be enabled by M227-027.
      --
      --  Make sure that once this is implemented, the mechanism for analysing
      --  single subprograms is not broken.

      --  pragma Assert (Nkind (Procedure_Spec) = N_Procedure_Specification);
      --
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
      Sub_Called                   : Node_Sets.Set     := Node_Sets.Empty_Set;
      Loops                        : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc                        : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      Subprogram : constant Entity_Id  := Get_Called_Entity (Call_Vertex);
      Scope      : constant Flow_Scope := Get_Flow_Scope (Call_Vertex);

      Ext_Relevant_To_Formal : constant Boolean :=
        Has_Extensions_Visible (Subprogram) or else
        Is_Class_Wide_Type (Get_Type (Formal, Scope));

      A        : V_Attributes     := Null_Attributes;
      Tmp_Used : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      Unused   : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

   begin
      A.Is_Parameter                 := True;
      A.Is_Discr_Or_Bounds_Parameter := Discriminants_Or_Bounds_Only;
      A.Subprograms_Called           := Sub_Called;
      A.Call_Vertex                  := Direct_Mapping_Id (Call_Vertex);
      A.Parameter_Actual             := Direct_Mapping_Id (Actual);
      A.Parameter_Formal             := Direct_Mapping_Id (Formal);
      A.Loops                        := Loops;
      A.Error_Location               := E_Loc;

      if In_Vertex then
         Tmp_Used := Get_Variables
           (Actual,
            Scope                => Scope,
            Local_Constants      => FA.Local_Constants,
            Fold_Functions       => True,
            Use_Computed_Globals => not FA.Generating_Globals,
            Consider_Extensions  => Ext_Relevant_To_Formal);

         for F of Tmp_Used loop
            if not Discriminants_Or_Bounds_Only
              or else Is_Record_Discriminant (F)
            then
               A.Variables_Used.Include (F);
            end if;
            if not Is_Bound (F) and then Has_Bounds (F, Scope) then
               A.Variables_Used.Include (F'Update (Facet => The_Bounds));
            end if;
         end loop;

         A.Variables_Explicitly_Used := A.Variables_Used;

      else
         declare
            Partial    : Boolean;
            Unused_Vc  : Boolean;
            Unused_Seq : Node_Lists.List;
            Classwide  : Boolean;
            Map_Root   : Flow_Id;
         begin
            --  We're interested in the map root, since we might have to do
            --  something about extensions.
            Get_Assignment_Target_Properties
              (Actual,
               Partial_Definition => Partial,
               View_Conversion    => Unused_Vc,
               Classwide          => Classwide,
               Map_Root           => Map_Root,
               Seq                => Unused_Seq);

            --  We have an unconditional addition to folded_function_checks for
            --  each actual anyway, so we can ignore the proof variables here.
            Untangle_Assignment_Target
              (N                    => Actual,
               Scope                => Scope,
               Local_Constants      => FA.Local_Constants,
               Use_Computed_Globals => not FA.Generating_Globals,
               Vars_Defined         => A.Variables_Defined,
               Vars_Used            => A.Variables_Explicitly_Used,
               Vars_Proof           => Unused,
               Partial_Definition   => Partial);

            if Ext_Relevant_To_Formal
              and then Extensions_Visible (Map_Root, Scope)
            then
               A.Variables_Defined.Include
                 (Map_Root'Update (Facet => Extension_Part));
            end if;

            A.Variables_Used := A.Variables_Explicitly_Used;

            if Partial then
               A.Variables_Used.Union (A.Variables_Defined);
            end if;

         end;
      end if;

      A.Is_Proof := Refers_To_Ghost (FA, A);
      Add_Volatile_Effects (A);
      return A;
   end Make_Parameter_Attributes;

   ----------------------------
   -- Make_Global_Attributes --
   ----------------------------

   function Make_Global_Attributes
     (FA                           : Flow_Analysis_Graphs;
      Call_Vertex                  : Node_Id;
      Global                       : Flow_Id;
      Discriminants_Or_Bounds_Only : Boolean;
      Loops                        : Node_Sets.Set;
      E_Loc                        : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      G     : constant Flow_Id    := Change_Variant (Global, Normal_Use);
      A     : V_Attributes        := Null_Attributes;
      Scope : constant Flow_Scope := Get_Flow_Scope (Call_Vertex);
      Tmp   : Flow_Id_Sets.Set;
   begin
      A.Is_Global_Parameter          := True;
      A.Is_Discr_Or_Bounds_Parameter := Discriminants_Or_Bounds_Only;
      A.Call_Vertex                  := Direct_Mapping_Id (Call_Vertex);
      A.Parameter_Formal             := Global;
      A.Loops                        := Loops;
      A.Error_Location               := E_Loc;

      case Global.Variant is
         when In_View =>
            Tmp := Flatten_Variable (G, Scope);
            if Extensions_Visible (G, Scope) then
               --  Tmp.Include (G'Update (Facet => The_Tag));
               Tmp.Include (G'Update (Facet => Extension_Part));
            end if;

            for F of Tmp loop
               if not Discriminants_Or_Bounds_Only or else
                 Is_Record_Discriminant (F)
               then
                  A.Variables_Used.Include (F);
               end if;

               if not Is_Bound (F) and then Has_Bounds (F, Scope) then
                  A.Variables_Used.Include (F'Update (Facet => The_Bounds));
               end if;
            end loop;

            A.Variables_Explicitly_Used := A.Variables_Used;

         when Out_View =>
            --  We do not need untangle_assignment_target as we only
            --  ever update the entire global.
            Tmp := Flatten_Variable (G, Scope);
            if Extensions_Visible (G, Scope) then
               --  We can't actually modify the tag, so this is not an
               --  omission.
               Tmp.Include (G'Update (Facet => Extension_Part));
            end if;
            A.Variables_Defined := Tmp;

         when others =>
            raise Program_Error;
      end case;

      A.Is_Proof := Refers_To_Ghost (FA, A);
      Add_Volatile_Effects (A, Global);
      return A;
   end Make_Global_Attributes;

   ----------------------------------------
   -- Make_Implicit_Parameter_Attributes --
   ----------------------------------------

   function Make_Implicit_Parameter_Attributes
     (FA          : Flow_Analysis_Graphs;
      Call_Vertex : Node_Id;
      Implicit    : Flow_Id;
      Loops       : Node_Sets.Set;
      E_Loc       : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      I     : constant Flow_Id    := Change_Variant (Implicit, Normal_Use);
      A     : V_Attributes        := Null_Attributes;
      Scope : constant Flow_Scope := Get_Flow_Scope (Call_Vertex);
   begin
      A.Is_Implicit_Parameter := True;
      A.Call_Vertex           := Direct_Mapping_Id (Call_Vertex);
      A.Parameter_Formal      := Implicit;
      A.Loops                 := Loops;
      A.Error_Location        := E_Loc;

      case Implicit.Variant is
         when In_View =>
            declare
               Implicit_Flat : constant Flow_Id_Sets.Set :=
                 Flatten_Variable (I, Scope);
            begin
               pragma Assert (A.Variables_Used.Is_Empty);
               pragma Assert (A.Variables_Explicitly_Used.Is_Empty);
               A.Variables_Used := Implicit_Flat;
               A.Variables_Explicitly_Used := Implicit_Flat;
            end;

         when Out_View =>
            pragma Assert (A.Variables_Defined.Is_Empty);
            A.Variables_Defined := Flatten_Variable (I, Scope);

         when others =>
            raise Program_Error;
      end case;

      A.Is_Proof := Refers_To_Ghost (FA, A);
      Add_Volatile_Effects (A, I);
      return A;
   end Make_Implicit_Parameter_Attributes;

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
     (FA    : Flow_Analysis_Graphs;
      F_Ent : Flow_Id;
      Mode  : Param_Mode;
      E_Loc : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A          : V_Attributes       := Null_Attributes;
      Entire_Var : constant Entity_Id :=
        Get_Direct_Mapping_Id (Entire_Variable (F_Ent));
   begin
      A.Error_Location     := E_Loc;
      A.Is_Constant        :=
        Ekind (Entire_Var) in E_In_Parameter | E_Loop_Parameter;
      A.Is_Function_Return := Ekind (Entire_Var) = E_Function;
      A.Is_Package_State   := Is_Package_State (Entire_Var);
      A.Mode               := Mode;

      case F_Ent.Variant is
         when Initial_Value =>
            A.Is_Initialized := Ekind (Entire_Var) in E_In_Out_Parameter |
                                                      E_In_Parameter     |
                                                      E_Loop_Parameter
              or else A.Mode in Initialized_Global_Modes
              or else In_Generic_Actual (Entire_Var);

            --  Is_Import is True for:
            --    * formal "in" and "in out" parameters
            --    * concurrent types (since they are implicit formal
            --      parameters)
            --    * components of protected objects
            --    * parts of task objects that are initialized
            A.Is_Import :=
              Ekind (Entire_Var) in E_In_Out_Parameter |
                                    E_In_Parameter     |
                                    E_Protected_Type   |
                                    E_Task_Type
              or else (Belongs_To_Concurrent_Type (F_Ent)
                         and then (Belongs_To_Protected_Type (F_Ent)
                                     or else Is_Default_Initialized (F_Ent)))
              or else In_Generic_Actual (Entire_Var);

            if Is_Discriminant (F_Ent)
              or else Is_Bound (F_Ent)
              or else Is_Record_Tag (F_Ent)
            then
               --  Discriminants, array bounds and tags are *always*
               --  initialized. They are also implicit imports if they are
               --  out parameters.
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
            --  Is_Export is True for:
            --    * formal "in" and "in out" parameters
            --    * function results
            --    * exported modes (modes "in", "out" and "in out")
            A.Is_Export := Ekind (Entire_Var) in E_In_Out_Parameter |
                                                 E_Out_Parameter    |
                                                 E_Function
              or else A.Mode in Exported_Global_Modes;

            if Is_Bound (F_Ent) then
               --  Array bounds are not exported.
               A.Is_Export := False;
            end if;

            A.Is_Loop_Parameter := Ekind (Entire_Var) = E_Loop_Parameter;

            A.Variables_Used := Flow_Id_Sets.To_Set (Change_Variant
                                                       (F_Ent, Normal_Use));
            A.Variables_Explicitly_Used := A.Variables_Used;

         when others =>
            raise Program_Error;
      end case;

      A.Is_Proof := Refers_To_Ghost (FA, A);

      return A;
   end Make_Variable_Attributes;

   -------------------------------------
   -- Make_Global_Variable_Attributes --
   -------------------------------------

   function Make_Global_Variable_Attributes
     (FA     : Flow_Analysis_Graphs;
      F      : Flow_Id;
      Mode   : Param_Mode;
      Uninit : Boolean           := False;
      E_Loc  : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Error_Location := E_Loc;
      A.Is_Global      := True;
      A.Is_Constant    := Mode in In_Global_Modes;
      A.Mode           := Mode;

      case F.Variant is
         when Initial_Value =>
            A.Is_Initialized := not Uninit
              and then Mode in Initialized_Global_Modes;

            if Is_Discriminant (F)
              or else Is_Bound (F)
              or else Is_Record_Tag (F)
            then
               --  Discriminants, array bounds and tags are *always*
               --  initialized imports.
               A.Is_Initialized := True;
               A.Is_Import      := True;
            end if;

            A.Is_Import         := A.Is_Initialized;
            A.Variables_Defined :=
              Flow_Id_Sets.To_Set (Change_Variant (F, Normal_Use));

         when Final_Value =>
            --  Array bounds are not exported.
            A.Is_Export := Mode in Exported_Global_Modes
              and then not Is_Bound (F);

            A.Variables_Used :=
              Flow_Id_Sets.To_Set (Change_Variant (F, Normal_Use));
            A.Variables_Explicitly_Used := A.Variables_Used;

         when others =>
            raise Program_Error;
      end case;

      A.Is_Proof := (Mode = Mode_Proof) or else Refers_To_Ghost (FA, A);

      return A;
   end Make_Global_Variable_Attributes;

   --------------------------------------------
   -- Make_Default_Initialization_Attributes --
   --------------------------------------------

   function Make_Default_Initialization_Attributes
     (FA    : Flow_Analysis_Graphs;
      Scope : Flow_Scope;
      F     : Flow_Id;
      Loops : Node_Sets.Set := Node_Sets.Empty_Set)
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

      A.Default_Init_Var  := F;
      A.Default_Init_Val  := DI;

      A.Variables_Defined := Flow_Id_Sets.To_Set (F);
      if Present (DI) then
         A.Variables_Used := Get_Variables
           (A.Default_Init_Val,
            Scope                => Scope,
            Local_Constants      => FA.Local_Constants,
            Fold_Functions       => False,
            Use_Computed_Globals => not FA.Generating_Globals);
         A.Variables_Explicitly_Used := A.Variables_Used;
      end if;
      A.Is_Proof          := Refers_To_Ghost (FA, A);

      Add_Volatile_Effects (A);
      return A;
   end Make_Default_Initialization_Attributes;

   --------------------------------------------
   -- Make_Package_Initialization_Attributes --
   --------------------------------------------

   function Make_Package_Initialization_Attributes
     (FA        : Flow_Analysis_Graphs;
      The_State : Flow_Id;
      Inputs    : Flow_Id_Sets.Set;
      Scope     : Flow_Scope;
      Loops     : Node_Sets.Set;
      E_Loc     : Node_Or_Entity_Id)
      return V_Attributes
   is
      A : V_Attributes;

      Split_State : constant Flow_Id_Sets.Set :=
        Flatten_Variable (The_State, Scope);

      Split_Inputs : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      --  We will get a relation from an initializes like X => Y. But X and
      --  Y may be records, and so we need to split up both the state and
      --  the list of inputs.
      for Input of Inputs loop
         Split_Inputs.Union (Flatten_Variable (Input, Scope));
      end loop;

      A := Make_Basic_Attributes
        (FA         => FA,
         Var_Def    => Split_State,
         Var_Ex_Use => Split_Inputs,
         Var_Im_Use =>
           (if Is_Initialized_At_Elaboration (The_State, Scope)
              and then Is_Initialized_In_Specification (The_State, Scope)
            then Split_State
            else Flow_Id_Sets.Empty_Set),
         Loops      => Loops,
         E_Loc      => E_Loc);
      A.Is_Package_Initialization := True;
      A.Is_Proof := Refers_To_Ghost (FA, A);
      return A;
   end Make_Package_Initialization_Attributes;

   ---------------------
   -- Refers_To_Ghost --
   ---------------------

   function Refers_To_Ghost
     (FA  : Flow_Analysis_Graphs;
      Atr : V_Attributes)
      return Boolean
   is
      All_Vars : constant Flow_Id_Sets.Set :=
        Atr.Variables_Used or Atr.Variables_Defined;
   begin
      return
        --  Check if the analyzed entity is a ghost
        Is_Ghost_Entity (FA.Analyzed_Entity)

        --  Check if any of the variables used or defined is a ghost
        or else
          (for some Var of All_Vars =>
             Var.Kind in Direct_Mapping | Record_Field
               and then Is_Ghost_Entity (Get_Direct_Mapping_Id (Var)))

        --  Check if any of the subprograms called is a ghost
        or else
          (for some Sub of Atr.Subprograms_Called =>
             Is_Ghost_Entity (Sub));
   end Refers_To_Ghost;

end Flow.Control_Flow_Graph.Utility;
