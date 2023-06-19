------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--      F L O W . C O N T R O L _ F L O W _ G R A P H . U T I L I T Y       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2013-2023, Capgemini Engineering              --
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

with Atree;                     use Atree;
with Flow_Utility;              use Flow_Utility;
with Sem_Aux;                   use Sem_Aux;
with SPARK_Definition.Annotate; use SPARK_Definition.Annotate;
with SPARK_Util.Subprograms;    use SPARK_Util.Subprograms;
with SPARK_Util.Types;          use SPARK_Util.Types;

package body Flow.Control_Flow_Graph.Utility is

   use type Flow_Id_Sets.Set;

   procedure Add_Volatile_Effects
     (A      : in out V_Attributes;
      Global : Flow_Id := Null_Flow_Id)
   with Pre => (if Present (Global) then Global.Variant = Normal_Use);
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

   -------------------------------
   -- Get_Reclamation_Functions --
   -------------------------------

   function Get_Reclamation_Functions
     (Typ : Type_Kind_Id)
      return Node_Sets.Set
   is
      Result : Node_Sets.Set;
   begin
      for Part of Get_Reclaimed_Parts (Typ) loop
         declare
            Func : constant Entity_Id :=
              Get_Reclamation_Check_Function (Part);
         begin
            if Present (Func) then
               Result.Include (Func);
            end if;
         end;
      end loop;
      return Result;
   end Get_Reclamation_Functions;

   ---------------------------
   -- Process_Discriminants --
   ---------------------------

   function Process_Discriminants (Intermediate_Vars_Used : Flow_Id_Sets.Set;
                                   Var_Defined            : Flow_Id)
                                   return Flow_Id_Sets.Set
   is
      Variables_Used : Flow_Id_Sets.Set;
      use type Ada.Containers.Count_Type;
   begin
      for Im_Var of Intermediate_Vars_Used loop

         --  ??? Check whether elements within Composite_Kind other than
         --  E_Record_Type and E_Private_Type are required here.
         if Im_Var.Kind = Record_Field
           and then Ekind (Im_Var.Node) in E_Record_Type | E_Private_Type
         then
            --  We have an intermediate "variable used" of the form T.X where
            --  T is a type and X a discriminant thereof. Such a construct may
            --  only be used to define a record component.
            pragma Assert
              (Im_Var.Component.Length = 1
               and then
               Ekind (Im_Var.Component.Last_Element) = E_Discriminant
               and then
               Var_Defined.Kind = Record_Field
               and then
               Var_Defined.Component.Length >= 1);
            --  There are two cases to consider:
            --  1) Var_Defined is a discriminant; in this case an inner
            --  discriminant (e.g. A.B.C.Y) references an outer one (e.g.
            --  A.B.X). The inner discriminant can only refer to another
            --  discriminant one layer "up", so to get the variable used we
            --  must chop Y and C from Var_Defined, then append X.
            --  2) Var_Defined is not a discriminant; this case is where a
            --  component (e.g. A.B.C.D) references a discriminant at a higher
            --  level (e.g. A.B.X). We must successively "chop" components from
            --  Var_Defined until we reach a layer whose type is T, then append
            --  X. Note that we obtain the type of the layer above the current
            --  component via a check of its Scope.

            declare
               Im_Var_Type : constant Entity_Id :=
                 Get_Direct_Mapping_Id (Im_Var);
               pragma Assert
                 (Im_Var_Type = Scope (Im_Var.Component.Last_Element));
               Var_Defined_Copy : Flow_Id := Var_Defined;
            begin
               if Is_Discriminant (Var_Defined) then
                  Var_Defined_Copy.Component.Delete_Last; --  1st Chop
               else
                  loop
                     if Scope (Var_Defined_Copy.Component.Last_Element) =
                       Im_Var_Type
                     then
                        exit;
                     else
                        Var_Defined_Copy.Component.Delete_Last;
                        --  Chop & continue
                     end if;
                  end loop;
               end if;

               pragma Assert (Scope (Var_Defined_Copy.Component.Last_Element) =
                                Im_Var_Type);

               Var_Defined_Copy.Component.Delete_Last; --  Final Chop
               Var_Defined_Copy.Component.Append
                 (Im_Var.Component.Last_Element);
               Variables_Used.Insert (Var_Defined_Copy);
            end;
         else
            Variables_Used.Insert (Im_Var);
         end if;

      end loop;
      return Variables_Used;
   end Process_Discriminants;

   ---------------------------
   -- Make_Basic_Attributes --
   ---------------------------

   function Make_Basic_Attributes
     (Var_Def    : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Var_Ex_Use : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Var_Im_Use : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      Subp_Calls : Call_Sets.Set       := Call_Sets.Empty_Set;
      Proof_Deps : Node_Sets.Set       := Node_Sets.Empty_Set;
      Vertex_Ctx : Vertex_Context;
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
      A.Subprogram_Calls          := Subp_Calls;
      A.Proof_Dependencies        := Proof_Deps;
      A.Loops                     := Vertex_Ctx.Current_Loops;
      A.In_Nested_Package         := Vertex_Ctx.In_Nested_Package;
      A.Warnings_Off              := Vertex_Ctx.Warnings_Off;
      A.Error_Location            := E_Loc;
      A.Pretty_Print_Kind         := Print_Hint;

      Add_Volatile_Effects (A);
      return A;
   end Make_Basic_Attributes;

   -------------------------------------
   -- Make_Extended_Return_Attributes --
   -------------------------------------

   function Make_Extended_Return_Attributes
     (Var_Def         : Flow_Id_Sets.Set;
      Var_Use         : Flow_Id_Sets.Set;
      Object_Returned : Entity_Id;
      Vertex_Ctx      : Vertex_Context;
      E_Loc           : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Is_Program_Node           := True;
      A.Variables_Defined         := Var_Def;
      A.Variables_Used            := Var_Use;
      A.Variables_Explicitly_Used := Var_Use;
      A.Loops                     := Vertex_Ctx.Current_Loops;
      A.Warnings_Off              := Vertex_Ctx.Warnings_Off;
      A.Error_Location            := E_Loc;
      A.Aux_Node                  := Object_Returned;

      Add_Volatile_Effects (A);
      return A;
   end Make_Extended_Return_Attributes;

   ---------------------------------
   -- Make_Sink_Vertex_Attributes --
   ---------------------------------

   function Make_Sink_Vertex_Attributes
     (Var_Use       : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Subp_Calls    : Call_Sets.Set     := Call_Sets.Empty_Set;
      Proof_Deps    : Node_Sets.Set     := Node_Sets.Empty_Set;
      Aspect        : Type_Aspect       := No_Aspect;
      Is_Assertion  : Boolean           := False;
      Is_Loop_Entry : Boolean           := False;
      Is_Fold_Check : Boolean           := False;
      Is_Type_Decl  : Boolean           := False;
      Vertex_Ctx    : Vertex_Context;
      E_Loc         : Node_Or_Entity_Id := Empty;
      Execution     : Execution_Kind_T  := Normal_Execution)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      if Is_Type_Decl then
         A.Variables_Read            := Var_Use;
      else
         A.Variables_Used            := Var_Use;
         A.Variables_Explicitly_Used := Var_Use;
      end if;

      A.Subprogram_Calls   := Subp_Calls;
      A.Proof_Dependencies := Proof_Deps;
      A.Is_Assertion       := Is_Assertion;
      A.Is_Loop_Entry      := Is_Loop_Entry;
      A.In_Nested_Package  := Vertex_Ctx.In_Nested_Package;
      A.Warnings_Off       := Vertex_Ctx.Warnings_Off;
      A.Error_Location     := E_Loc;
      A.Execution          := Execution;

      if Is_Fold_Check then
         A.Pretty_Print_Kind := Pretty_Print_Folded_Function_Check;
      else
         case Aspect is
            when DIC =>
               A.Pretty_Print_Kind := Pretty_Print_DIC;
            when No_Aspect =>
               null;
         end case;
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
     (Callsite   : Node_Id;
      Var_Use    : Flow_Id_Sets.Set  := Flow_Id_Sets.Empty_Set;
      Subp_Calls : Call_Sets.Set     := Call_Sets.Empty_Set;
      Proof_Deps : Node_Sets.Set     := Node_Sets.Empty_Set;
      Vertex_Ctx : Vertex_Context;
      E_Loc      : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
      pragma Unreferenced (Callsite);
   begin
      A.Variables_Explicitly_Used := Var_Use;
      A.Variables_Used            := Var_Use;
      A.Subprogram_Calls          := Subp_Calls;
      A.Proof_Dependencies        := Proof_Deps;
      A.Is_Program_Node           := True;
      A.Loops                     := Vertex_Ctx.Current_Loops;
      A.In_Nested_Package         := Vertex_Ctx.In_Nested_Package;
      A.Warnings_Off              := Vertex_Ctx.Warnings_Off;
      A.Is_Callsite               := True;
      A.Error_Location            := E_Loc;

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
      Formal                       : Entity_Id;
      In_Vertex                    : Boolean;
      Discriminants_Or_Bounds_Only : Boolean;
      Subp_Calls                   : Call_Sets.Set   := Call_Sets.Empty_Set;
      Proof_Deps                   : Node_Sets.Set   := Node_Sets.Empty_Set;
      Vertex_Ctx                   : Vertex_Context;
      E_Loc                        : Node_Or_Entity_Id)
      return V_Attributes
   is
      Subprogram : constant Entity_Id := Get_Called_Entity (Call_Vertex);
      Scope      : Flow_Scope renames FA.B_Scope;

      Ext_Relevant_To_Formal : constant Boolean :=
        Has_Extensions_Visible (Subprogram) or else
        Is_Class_Wide_Type (Get_Type (Formal, Scope));

      A : V_Attributes := Null_Attributes;

   begin
      A.Is_Parameter                 := True;
      A.Is_Discr_Or_Bounds_Parameter := Discriminants_Or_Bounds_Only;
      A.Subprogram_Calls             := Subp_Calls;
      A.Proof_Dependencies           := Proof_Deps;
      A.Call_Vertex                  := Direct_Mapping_Id (Call_Vertex);
      A.Parameter_Actual             := Direct_Mapping_Id (Actual);
      A.Parameter_Formal             := Direct_Mapping_Id (Formal);
      A.Loops                        := Vertex_Ctx.Current_Loops;
      A.In_Nested_Package            := Vertex_Ctx.In_Nested_Package;
      A.Warnings_Off                 := Vertex_Ctx.Warnings_Off;
      A.Error_Location               := E_Loc;

      if In_Vertex then
         declare
            Used : constant Flow_Id_Sets.Set :=
              Get_Variables
                (Actual,
                 Scope                => Scope,
                 Target_Name          => Null_Flow_Id,
                 Fold_Functions       => Inputs,
                 Use_Computed_Globals => not FA.Generating_Globals,
                 Consider_Extensions  => Ext_Relevant_To_Formal);
         begin
            for F of Used loop
               if not Discriminants_Or_Bounds_Only
                 or else Is_Discriminant (F)
               then
                  A.Variables_Used.Include (F);
               end if;
               if not Is_Bound (F) and then Has_Bounds (F, Scope) then
                  A.Variables_Used.Include
                    ((F with delta Facet => The_Bounds));
               end if;
            end loop;

            A.Variables_Explicitly_Used := A.Variables_Used;
         end;

      --  For a "null" appearing as actual parameter of mode IN where the
      --  formal parameter is of an owning access type do nothing. Such a
      --  parameter doesn't define nor use any variables.

      elsif not Is_Null_Owning_Access (Actual) then

         declare
            Partial    : Boolean;
            Unused_Vc  : Boolean;
            Unused_Seq : Node_Lists.List;
            Map_Root   : Flow_Id;

         begin
            --  We're interested in the map root, since we might have to do
            --  something about extensions.
            Get_Assignment_Target_Properties
              (Actual,
               Partial_Definition => Partial,
               View_Conversion    => Unused_Vc,
               Map_Root           => Map_Root,
               Seq                => Unused_Seq);

            --  We have an unconditional addition to folded_function_checks for
            --  each actual anyway, so we can ignore the proof variables here.
            Untangle_Assignment_Target
              (N                    => Actual,
               Scope                => Scope,
               Use_Computed_Globals => not FA.Generating_Globals,
               Vars_Defined         => A.Variables_Defined,
               Vars_Used            => A.Variables_Explicitly_Used,
               Partial_Definition   => Partial);

            if Ext_Relevant_To_Formal
              and then Extensions_Visible (Map_Root, Scope)
            then
               A.Variables_Defined.Include
                 ((Map_Root with delta Facet => Extension_Part));
            end if;

            A.Variables_Used := A.Variables_Explicitly_Used;

            if Partial then
               A.Variables_Used.Union (A.Variables_Defined);
            end if;

         end;
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
      Scope                        : Flow_Scope;
      Discriminants_Or_Bounds_Only : Boolean;
      Vertex_Ctx                   : Vertex_Context;
      Is_Assertion                 : Boolean           := False;
      E_Loc                        : Node_Or_Entity_Id := Empty)
      return V_Attributes
   is
      G : constant Flow_Id := Change_Variant (Global, Normal_Use);
      A : V_Attributes     := Null_Attributes;

      Tmp : Flow_Id_Sets.Set;
   begin
      A.Is_Global_Parameter          := True;
      A.Is_Discr_Or_Bounds_Parameter := Discriminants_Or_Bounds_Only;
      A.Call_Vertex                  := Direct_Mapping_Id (Call_Vertex);
      A.Parameter_Formal             := Global;
      A.Loops                        := Vertex_Ctx.Current_Loops;
      A.In_Nested_Package            := Vertex_Ctx.In_Nested_Package;
      A.Warnings_Off                 := Vertex_Ctx.Warnings_Off;
      A.Error_Location               := E_Loc;
      A.Is_Assertion                 := Is_Assertion;

      case Global.Variant is
         when In_View =>
            Tmp := Flatten_Variable (G, Scope);
            if Extensions_Visible (G, Scope) then
               --  Tmp.Include ((G with delta Facet => The_Tag));
               Tmp.Include ((G with delta Facet => Extension_Part));
            end if;

            for F of Tmp loop
               if not Discriminants_Or_Bounds_Only
                 or else Is_Discriminant (F)
               then
                  A.Variables_Used.Include (F);
               end if;

               if not Is_Bound (F) and then Has_Bounds (F, Scope) then
                  A.Variables_Used.Include
                    ((F with delta Facet => The_Bounds));
               end if;
            end loop;

            A.Variables_Explicitly_Used := A.Variables_Used;

         when Out_View =>
            --  We do not need untangle_assignment_target as we only
            --  ever update the entire global.
            Tmp := Flatten_Variable (G, Scope);
            if Extensions_Visible (G, Scope) then
               --  We can't actually modify the tag, so this is not an omission
               Tmp.Include ((G with delta Facet => Extension_Part));
            end if;
            A.Variables_Defined := Tmp;

         when others =>
            raise Program_Error;
      end case;

      Add_Volatile_Effects (A, G);
      return A;
   end Make_Global_Attributes;

   ----------------------------------------
   -- Make_Implicit_Parameter_Attributes --
   ----------------------------------------

   function Make_Implicit_Parameter_Attributes
     (FA          : Flow_Analysis_Graphs;
      Call_Vertex : Node_Id;
      In_Vertex   : Boolean;
      Scope       : Flow_Scope;
      Subp_Calls  : Call_Sets.Set   := Call_Sets.Empty_Set;
      Proof_Deps  : Node_Sets.Set   := Node_Sets.Empty_Set;
      Vertex_Ctx  : Vertex_Context;
      E_Loc       : Node_Or_Entity_Id)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;

      Subprogram : constant Entity_Id := Get_Called_Entity (Call_Vertex);

   begin
      --  External calls appear in the code as:
      --
      --    PO.Proc (Actual1, Actual2, ...);
      --
      --  but we handle them very much like:
      --
      --    Proc (PO, Actual1, Actual2, ...);
      --
      --  and set attributes very much like in Make_Parameter_Attributes.
      --
      --  Note: we can't simply reuse that routine because it is (rightly)
      --  flooded with assertions that check for ordinary formal parameters.

      if Is_External_Call (Call_Vertex) then
         A.Is_Parameter       := True;
         A.Subprogram_Calls   := Subp_Calls;
         A.Proof_Dependencies := Proof_Deps;
         A.Call_Vertex        := Direct_Mapping_Id (Call_Vertex);
         A.Parameter_Actual   :=
           Direct_Mapping_Id (Prefix (Name (Call_Vertex)));
         A.Parameter_Formal   :=
           Direct_Mapping_Id (Sinfo.Nodes.Scope (Subprogram));
         A.Loops              := Vertex_Ctx.Current_Loops;
         A.Warnings_Off       := Vertex_Ctx.Warnings_Off;
         A.Error_Location     := E_Loc;

         if In_Vertex then
            declare
               Used : constant Flow_Id_Sets.Set :=
                 Get_Variables
                   (N                    => Prefix (Name (Call_Vertex)),
                    Scope                => Scope,
                    Target_Name          => Null_Flow_Id,
                    Fold_Functions       => Inputs,
                    Use_Computed_Globals => not FA.Generating_Globals);
            begin
               A.Variables_Used := Used;
               for F of Used loop
                  if not Is_Bound (F) and then Has_Bounds (F, Scope) then
                     A.Variables_Used.Include
                       ((F with delta Facet => The_Bounds));
                  end if;
               end loop;

               A.Variables_Explicitly_Used := A.Variables_Used;
            end;
         else
            declare
               Partial : Boolean;

            begin
               --  We have an unconditional addition to folded_function_checks
               --  for each actual anyway, so we can ignore the proof variables
               --  here.
               Untangle_Assignment_Target
                 (N                    => Prefix (Name (Call_Vertex)),
                  Scope                => Scope,
                  Use_Computed_Globals => not FA.Generating_Globals,
                  Vars_Defined         => A.Variables_Defined,
                  Vars_Used            => A.Variables_Explicitly_Used,
                  Partial_Definition   => Partial);

               A.Variables_Used := A.Variables_Explicitly_Used;

               if Partial then
                  A.Variables_Used.Union (A.Variables_Defined);
               end if;
            end;
         end if;

         Add_Volatile_Effects (A);

      --  In internal calls the implicit parameter behaves more like a global,
      --  i.e. we don't have an actual expression for it.

      else
         declare
            Implicit : constant Flow_Id :=
              Direct_Mapping_Id (Sinfo.Nodes.Scope (Subprogram));

            Implicit_Flat : constant Flow_Id_Sets.Set :=
              Flatten_Variable (Implicit, Scope);
            --  Flat view of the implicit parameter

         begin
            A.Is_Implicit_Parameter := True;
            A.Call_Vertex           := Direct_Mapping_Id (Call_Vertex);
            A.Parameter_Formal      :=
              Change_Variant (Implicit,
                              (if In_Vertex then In_View else Out_View));
            A.Loops                 := Vertex_Ctx.Current_Loops;
            A.In_Nested_Package     := Vertex_Ctx.In_Nested_Package;
            A.Warnings_Off          := Vertex_Ctx.Warnings_Off;
            A.Error_Location        := E_Loc;

            if In_Vertex then
               A.Variables_Used            := Implicit_Flat;
               A.Variables_Explicitly_Used := Implicit_Flat;
            else
               A.Variables_Defined         := Implicit_Flat;
            end if;

            --  For internal calls the implicit parameter acts as an ordinary
            --  record object and cannot be annotated with effective reads or
            --  writes.

            pragma Assert (not Has_Effective_Reads (Implicit));
            pragma Assert (not Has_Effective_Writes (Implicit));
         end;
      end if;

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
     (F_Ent      : Flow_Id;
      Mode       : Param_Mode;
      Proof_Deps : Node_Sets.Set     := Node_Sets.Empty_Set;
      E_Loc      : Node_Or_Entity_Id := Empty;
      S          : Flow_Scope        := Null_Flow_Scope)
      return V_Attributes
   is
      A          : V_Attributes       := Null_Attributes;
      Entire_Var : constant Entity_Id :=
        Get_Direct_Mapping_Id (Entire_Variable (F_Ent));

   begin
      A.Error_Location     := E_Loc;
      A.Is_Constant        :=
        Ekind (Entire_Var) in E_In_Parameter | E_Loop_Parameter;
      A.Mode               := Mode;
      A.Proof_Dependencies := Proof_Deps;

      case F_Ent.Variant is
         when Initial_Value =>

            A.Is_Initialized := A.Mode in Mode_In | Mode_In_Out
              or else Ekind (Entire_Var) in E_Loop_Parameter | E_Constant
              or else (not Is_In_Analyzed_Files (Entire_Var)
                         and then
                       Is_Initialized_At_Elaboration (Entire_Var, S));

            --  Is_Import is True for:
            --    * formal "in" and "in out" parameters
            --    * concurrent types (since they are implicit formal
            --      parameters), they components, discriminants and Part_Ofs
            A.Is_Import :=
              A.Mode in Mode_In | Mode_In_Out;

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

            A.Variables_Defined := Flow_Id_Sets.To_Set (Change_Variant
                                                          (F_Ent, Normal_Use));

         when Final_Value =>
            A.Is_Export :=
              A.Mode in Exported_Global_Modes
              and then not Is_Bound (F_Ent);

            A.Variables_Used := Flow_Id_Sets.To_Set (Change_Variant
                                                       (F_Ent, Normal_Use));
            A.Variables_Explicitly_Used := A.Variables_Used;

         when others =>
            raise Program_Error;
      end case;

      return A;
   end Make_Variable_Attributes;

   -------------------------------------
   -- Make_Global_Variable_Attributes --
   -------------------------------------

   function Make_Global_Variable_Attributes
     (F    : Flow_Id;
      Mode : Param_Mode)
      return V_Attributes
   is
      A : V_Attributes := Null_Attributes;
   begin
      A.Is_Global   := True;
      A.Is_Constant := Mode in In_Global_Modes;
      A.Mode        := Mode;

      case F.Variant is
         when Initial_Value =>
            if Is_Discriminant (F)
              or else Is_Bound (F)
              or else Is_Record_Tag (F)
            then
               --  Discriminants, array bounds and tags are *always*
               --  initialized imports.
               A.Is_Initialized := True;
               A.Is_Import      := True;
            else
               A.Is_Initialized := Mode in Initialized_Global_Modes;
               A.Is_Import      := A.Is_Initialized;
            end if;

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

      return A;
   end Make_Global_Variable_Attributes;

   --------------------------------------------
   -- Make_Default_Initialization_Attributes --
   --------------------------------------------

   function Make_Default_Initialization_Attributes
     (FA         : Flow_Analysis_Graphs;
      Scope      : Flow_Scope;
      F          : Flow_Id;
      Vertex_Ctx : Vertex_Context)
      return V_Attributes
   is
      A  : V_Attributes     := Null_Attributes;
      DI : constant Node_Id := Get_Default_Initialization (F);
   begin
      A.Is_Default_Init   := True;
      A.Loops             := Vertex_Ctx.Current_Loops;
      A.In_Nested_Package := Vertex_Ctx.In_Nested_Package;
      A.Warnings_Off      := Vertex_Ctx.Warnings_Off;
      if Present (DI) then
         A.Error_Location := DI;
      else
         A.Error_Location := Etype (Get_Direct_Mapping_Id (F));
      end if;

      A.Default_Init_Var  := F;
      A.Default_Init_Val  := DI;

      A.Variables_Defined := Flow_Id_Sets.To_Set (F);
      if Present (DI) then
         A.Variables_Used :=
           Process_Discriminants
             (Intermediate_Vars_Used =>
                Get_All_Variables
                  (N                    => A.Default_Init_Val,
                   Scope                => Scope,
                   Target_Name          => Null_Flow_Id,
                   Use_Computed_Globals => not FA.Generating_Globals),
              Var_Defined            => F);
         A.Variables_Explicitly_Used := A.Variables_Used;
      end if;

      Add_Volatile_Effects (A);
      return A;
   end Make_Default_Initialization_Attributes;

   --------------------------------------------
   -- Make_Package_Initialization_Attributes --
   --------------------------------------------

   function Make_Package_Initialization_Attributes
     (The_State  : Flow_Id;
      Inputs     : Flow_Id_Sets.Set;
      Scope      : Flow_Scope;
      Vertex_Ctx : Vertex_Context;
      E_Loc      : Node_Or_Entity_Id)
      return V_Attributes
   is
      A : V_Attributes;

      Split_State : constant Flow_Id_Sets.Set :=
        (if Present (The_State)
         then Flatten_Variable (The_State, Scope)
         else Flow_Id_Sets.Empty_Set);

      Split_Inputs : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      --  We will get a relation from an initializes like X => Y. But X and
      --  Y may be records, and so we need to split up both the state and
      --  the list of inputs.
      for Input of Inputs loop
         Split_Inputs.Union (Flatten_Variable (Input, Scope));
      end loop;

      A := Make_Basic_Attributes
        (Var_Def       => Split_State,
         Var_Ex_Use    => Split_Inputs,
         Var_Im_Use    =>
           (if Present (The_State)
              and then Is_Initialized_At_Elaboration (The_State, Scope)
              and then Is_Initialized_In_Specification (The_State, Scope)
            then Split_State
            else Flow_Id_Sets.Empty_Set),
         Vertex_Ctx    => Vertex_Ctx,
         E_Loc         => E_Loc);
      A.Is_Package_Initialization := True;
      return A;
   end Make_Package_Initialization_Attributes;

end Flow.Control_Flow_Graph.Utility;
