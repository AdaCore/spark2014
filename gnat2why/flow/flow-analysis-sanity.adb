------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . A N A L Y S I S . S A N I T Y                  --
--                                                                          --
--                                B o d y                                   --
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

--  This package implements a variety of sanity checks that are run before
--  the rest of flow analysis is performed.

with Nlists;                         use Nlists;
with Sem_Aux;                        use Sem_Aux;
with Sem_Util;                       use Sem_Util;
with Sinfo;                          use Sinfo;
with Snames;                         use Snames;

with Checked_Types;                  use Checked_Types;
with Gnat2Why_Args;
with SPARK_Definition;               use SPARK_Definition;
with SPARK_Util.Subprograms;         use SPARK_Util.Subprograms;
with SPARK_Util.Types;               use SPARK_Util.Types;
with SPARK_Util;                     use SPARK_Util;
with VC_Kinds;                       use VC_Kinds;

with Flow_Error_Messages;            use Flow_Error_Messages;
with Flow_Utility;                   use Flow_Utility;
with Flow_Refinement;                use Flow_Refinement;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;

package body Flow.Analysis.Sanity is

   use type Flow_Graphs.Vertex_Id;
   use type Flow_Id_Sets.Set;

   ---------------------------------
   -- Check_Function_Side_Effects --
   ---------------------------------

   procedure Check_Function_Side_Effects
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean)
   is
      Globals : Global_Flow_Ids;

   begin
      Sane := True;

      if Ekind (FA.Analyzed_Entity) = E_Function then

         Get_Globals (Subprogram => FA.Analyzed_Entity,
                      Scope      => FA.B_Scope,
                      Classwide  => False,
                      Globals    => Globals);

         if not Globals.Outputs.Is_Empty then

            Sane := False;

            for G of Globals.Outputs loop
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "function with output global & " &
                              "is not allowed in SPARK",
                  N        => FA.Analyzed_Entity,
                  F1       => G,
                  Severity => Error_Kind,
                  Tag      => Side_Effects);
            end loop;

            if Gnat2Why_Args.Debug_Mode then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "flow analysis of & abandoned due to " &
                              "function with side effects",
                  N        => FA.Analyzed_Entity,
                  Severity => Error_Kind,
                  F1       => Direct_Mapping_Id (FA.Analyzed_Entity));
            end if;
         end if;
      end if;
   end Check_Function_Side_Effects;

   -----------------------
   -- Check_Expressions --
   -----------------------

   procedure Check_Expressions
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean)
   is
      procedure Check_Actuals (E : Entity_Id)
      with Pre => Ekind (E) = E_Package;
      --  Check SPARK RM 4.4(2) rule about:
      --  * a generic actual parameter corresponding to a generic formal object
      --    having mode in
      --  where E is either a wrapper package (for generic subprograms) or a
      --  package instance (for generic packages).

      procedure Check_Component_Declaration (N : Node_Id)
      with Pre => Nkind (N) = N_Component_Declaration;
      --  Check both the default expression of a component declaration and
      --  its subtype constraint.

      procedure Check_Default_Expression (N : Node_Id)
      with Pre => Nkind (N) in N_Component_Declaration
                             | N_Discriminant_Specification;
      --  Check the default expression of component or discriminant, if
      --  present, i.e. SPARK RM 4.4(2) rules about:
      --  * the default expression of a component declaration
      --  * the default expression of a discriminant_specification

      function Check_Name_Index_And_Slice (N : Node_Id) return Traverse_Result;
      --  Check SPARK RM 4.4(2) rule about:
      --  * an indexing expression of an indexed component or the discrete
      --    range of a slice in an object renaming declaration which renames
      --    part of that index or slice.

      procedure Check_Name_Indexes_And_Slices is new
        Traverse_More_Proc (Check_Name_Index_And_Slice);

      procedure Check_Subtype_Constraints (N : Node_Id);
      --  Check that subtype constraints do not have variable inputs

      procedure Check_Type_Declaration (N : Node_Id)
      with Pre => Nkind (N) in N_Full_Type_Declaration
                             | N_Subtype_Declaration
                             | N_Incomplete_Type_Declaration
                             | N_Private_Type_Declaration
                             | N_Private_Extension_Declaration;
      --  Check if the expressions for the type declaration N have variable
      --  inputs. In particular this enforces SPARK RM 4.4(2) by checking:
      --  * a constraint other than the range of a loop parameter specification
      --  * a Dynamic_Predicate aspect specification
      --  * a Type_Invariant aspect specification

      procedure Check_Constrained_Array_Definition (N : Node_Id)
      with Pre => Nkind (N) in N_Full_Type_Declaration
                             | N_Object_Declaration;
      --  Check if the constrained array definition in N has variable inputs,
      --  as per SPARK RM 4.4(2);

      procedure Detect_Variable_Inputs
        (N        : Node_Id;
         Err_Desc : String;
         Err_Node : Node_Id);
      --  Emit error for any object referenced within N which does NOT denote
      --  a constant, a bound or a discriminant (of an enclosing concurrent
      --  type).

      procedure Traverse_Declarations_And_HSS       (N : Node_Id);
      procedure Traverse_Declarations_Or_Statements (L : List_Id);
      procedure Traverse_Declaration_Or_Statement   (N : Node_Id);
      procedure Traverse_Handled_Statement_Sequence (N : Node_Id);
      --  Traverse declarations and statements

      procedure Traverse_Component_List             (N : Node_Id)
      with Pre => Nkind (N) = N_Component_List;
      procedure Traverse_Component_Items            (L : List_Id);
      procedure Traverse_Discriminants              (N : Node_Id);
      procedure Traverse_Variant_Part               (N : Node_Id)
      with Pre => Nkind (N) = N_Variant_Part;
      --  Traversals for components and discriminants
      --
      --  Note: discriminants appear in various nodes; components appear in
      --  protected types and record types (both as immediate children or in
      --  arbitrarily nested variant parts).

      function Variables (N : Node_Id) return Flow_Id_Sets.Set
      is
        (Get_Variables (N,
                        Scope                   => FA.B_Scope,
                        Fold_Functions          => False,
                        Use_Computed_Globals    => True,
                        Expand_Internal_Objects => True));
      --  Wrapper around Get_Variables

      -------------------
      -- Check_Actuals --
      -------------------

      procedure Check_Actuals (E : Entity_Id) is
         Formal : Entity_Id := First_Entity (E);

      begin
         while Present (Formal) loop
            declare
               Decl : constant Node_Id := Parent (Formal);

            begin
               if Nkind (Decl) = N_Object_Declaration
                 and then Present (Corresponding_Generic_Association (Decl))
                 and then Constant_Present (Decl)
               then
                  Detect_Variable_Inputs
                    (N        => Expression (Decl),
                     Err_Desc => "actual for formal object with mode in",
                     Err_Node => Decl);
               end if;
            end;

            Next_Entity (Formal);
         end loop;
      end Check_Actuals;

      ---------------------------------
      -- Check_Component_Declaration --
      ---------------------------------

      procedure Check_Component_Declaration (N : Node_Id) is
      begin
         Check_Default_Expression (N);

         --  Check that the subtype constraint for the component, if present,
         --  does not depend on variable inputs.

         declare
            S_Indication_Mark : constant Node_Id :=
              Subtype_Indication (Component_Definition (N));

         begin
            case Nkind (S_Indication_Mark) is
               --  Subtype either points to a constraint, for example
               --  "String (1 .. 10)".

               when N_Subtype_Indication =>
                  Check_Subtype_Constraints
                    (Constraint (S_Indication_Mark));

               --  or to a type, for example "Integer", or "Standard.Integer"

               when N_Identifier | N_Expanded_Name =>
                  pragma Assert
                    (Is_Type (Entity (S_Indication_Mark)));

               when others =>
                  raise Program_Error;

            end case;
         end;
      end Check_Component_Declaration;

      ------------------------------
      -- Check_Default_Expression --
      ------------------------------

      procedure Check_Default_Expression (N : Node_Id) is
         Default_Expression : constant Node_Id := Expression (N);

      begin
         if Present (Default_Expression) then
            Detect_Variable_Inputs
              (N        => Default_Expression,
               Err_Desc => "default initialization",
               Err_Node => Default_Expression);
         end if;
      end Check_Default_Expression;

      --------------------------------
      -- Check_Name_Index_And_Slice --
      --------------------------------

      function Check_Name_Index_And_Slice (N : Node_Id) return Traverse_Result
      is
      begin
         case Nkind (N) is
            when N_Indexed_Component =>
               declare
                  Expr : Node_Id := First (Expressions (N));

               begin
                  loop
                     Detect_Variable_Inputs
                       (N        => Expr,
                        Err_Desc => "renamed index",
                        Err_Node => Expr);
                     Next (Expr);
                     exit when No (Expr);
                  end loop;
               end;

            when N_Slice =>
               Detect_Variable_Inputs
                 (N        => Discrete_Range (N),
                  Err_Desc => "renamed slice",
                  Err_Node => Discrete_Range (N));

            when others =>
               null;
         end case;

         return OK; -- Keep searching in case of nested prefixes
      end Check_Name_Index_And_Slice;

      -------------------------------
      -- Check_Subtype_Constraints --
      -------------------------------

      procedure Check_Subtype_Constraints (N : Node_Id) is
      begin
         case Nkind (N) is
            when N_Range =>
               declare
                  Lo : constant Node_Id := Low_Bound (N);
                  Hi : constant Node_Id := High_Bound (N);

               begin
                  Detect_Variable_Inputs
                    (N        => Lo,
                     Err_Desc => "subtype constraint",
                     Err_Node => Lo);

                  Detect_Variable_Inputs
                    (N        => Hi,
                     Err_Desc => "subtype constraint",
                     Err_Node => Hi);
               end;

            when N_Range_Constraint =>
               declare
                  Range_Expr : constant Node_Id := Range_Expression (N);

                  Lo : constant Node_Id := Low_Bound (Range_Expr);
                  Hi : constant Node_Id := High_Bound (Range_Expr);

               begin
                  Detect_Variable_Inputs
                    (N        => Lo,
                     Err_Desc => "subtype constraint",
                     Err_Node => Lo);

                  Detect_Variable_Inputs
                    (N        => Hi,
                     Err_Desc => "subtype constraint",
                     Err_Node => Hi);
               end;

            when N_Index_Or_Discriminant_Constraint =>
               declare
                  Constraint : Node_Id := First (Constraints (N));

               begin
                  loop
                     Detect_Variable_Inputs
                       (N        => Constraint,
                        Err_Desc => "subtype constraint",
                        Err_Node => Constraint);
                     Next (Constraint);
                     exit when No (Constraint);
                  end loop;
               end;

            when N_Delta_Constraint
               | N_Digits_Constraint
            =>

               --  Ada LRM requires these constraints to be static, so no
               --  further action required here.

               null;

            when others =>
               raise Program_Error;
         end case;
      end Check_Subtype_Constraints;

      ----------------------------------------
      -- Check_Constrained_Array_Definition --
      ----------------------------------------

      procedure Check_Constrained_Array_Definition (N : Node_Id) is
         Typ_Def : constant Node_Id :=
           (if Nkind (N) = N_Full_Type_Declaration
            then Type_Definition (N)
            else Object_Definition (N));
      begin
         if Nkind (Typ_Def) = N_Constrained_Array_Definition then
            declare
               Sub_Constraint : Node_Id :=
                 First (Discrete_Subtype_Definitions (Typ_Def));

            begin
               loop
                  case Nkind (Sub_Constraint) is
                     when N_Range =>
                        Check_Subtype_Constraints (Sub_Constraint);

                     when N_Subtype_Indication =>
                        Check_Subtype_Constraints
                          (Constraint (Sub_Constraint));

                     when N_Identifier | N_Expanded_Name =>
                        pragma Assert
                          (Is_Type (Entity (Sub_Constraint)));

                     when others =>
                        raise Program_Error;
                  end case;

                  Next (Sub_Constraint);

                  exit when No (Sub_Constraint);
               end loop;
            end;
         end if;
      end Check_Constrained_Array_Definition;

      ----------------------------
      -- Check_Type_Declaration --
      ----------------------------

      procedure Check_Type_Declaration (N : Node_Id) is
         Typ : constant Type_Id := Defining_Identifier (N);

      begin
         --  Check that the type predicate expression, if present, does not
         --  have variable inputs. We don't use Has_Predicates because in case
         --  of a type with a completion will return True both for the type
         --  declaration and the completion and we don't want to have duplicate
         --  checks.

         if Present (Get_Pragma (Typ, Pragma_Predicate)) then
            Detect_Variable_Inputs
              (N        => Get_Expr_From_Return_Only_Func
                             (Predicate_Function (Typ)),
               Err_Desc => "predicate",
               Err_Node => Typ);
         end if;

         --  Check that the type invariant expression, if present, does not
         --  have variable inputs. Has_Invariants_In_SPARK operates on the
         --  public view of a type and therefore we call it on private type
         --  declarations or extensions.

         if Nkind (N) in N_Private_Type_Declaration
                       | N_Private_Extension_Declaration
           and then Has_Invariants_In_SPARK (Typ)
         then
            declare
               Expr : constant Node_Id :=
                 Get_Expr_From_Check_Only_Proc (Invariant_Procedure (Typ));

               Funs : constant Node_Sets.Set :=
                 Get_Functions (Expr, Include_Predicates => False);

            begin
               --  Check 7.3.2(3) [which is really 4.4(2)] (no variable inputs)

               Detect_Variable_Inputs
                 (N        => Expr,
                  Err_Desc => "invariant",
                  Err_Node => Full_View (Typ));

               --  Check 7.3.2(5) (no calls to boundary subprograms)

               for F of Funs loop
                  if Is_Boundary_Subprogram_For_Type (F, Typ) then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      =>
                          "cannot call boundary subprogram & " &
                          "for type & in its own invariant",
                        Severity => High_Check_Kind,
                        Tag      => Call_In_Type_Invariant,
                        N        => Full_View (Typ),
                        F1       => Direct_Mapping_Id (F),
                        F2       => Direct_Mapping_Id (Typ),
                        SRM_Ref  => "7.3.2(5)");
                  end if;
               end loop;
            end;
         end if;

         --  Check that the subtype constraint, if present, does not depend
         --  on variable inputs.

         if Nkind (N) in N_Subtype_Declaration
                       | N_Full_Type_Declaration
                       | N_Private_Extension_Declaration
             and then
               (not Is_Internal (Typ)
                or else (Nkind (N) = N_Full_Type_Declaration
                         and then Present (Incomplete_View (N)))
                or else Is_Derived_Type (Typ))
         then
            declare
               S_Indication : Node_Id;

            begin
               --  Find the subtype indication

               case Nkind (N) is
                  when N_Full_Type_Declaration =>
                     declare
                        Typ_Def : constant Node_Id := Type_Definition (N);

                     begin
                        S_Indication :=
                          (case Nkind (Typ_Def) is
                              when N_Derived_Type_Definition =>
                                 Subtype_Indication (Typ_Def),
                              when N_Array_Type_Definition =>
                                 Subtype_Indication
                             (Component_Definition (Typ_Def)),
                              when others => Empty);
                     end;

                  when N_Subtype_Declaration
                     | N_Private_Extension_Declaration
                  =>
                     S_Indication := Subtype_Indication (N);

                  when others =>
                     raise Program_Error;
               end case;

               if Present (S_Indication)
                 and then Nkind (S_Indication) = N_Subtype_Indication
               then
                  Check_Subtype_Constraints
                    (Constraint (S_Indication));
               end if;
            end;
         end if;

         --  Special case for N_Constrained_Array_Definition. Check that its
         --  subtype constraints do not depend on variable inputs.

         if Nkind (N) = N_Full_Type_Declaration then
            Check_Constrained_Array_Definition (N);
         end if;

      end Check_Type_Declaration;

      ---------------------------
      -- Detect_Variable_Inputs --
      ---------------------------

      procedure Detect_Variable_Inputs
        (N        : Node_Id;
         Err_Desc : String;
         Err_Node : Node_Id)
      is
         function Is_Within_Protected_Function return Boolean;
         --  Returns True if we are inside a protected function, False if
         --  inside a protected procedure or entry, and crashes otherwise.

         procedure Emit_Error (F : Flow_Id);

         ----------------------------------
         -- Is_Within_Protected_Function --
         ----------------------------------

         function Is_Within_Protected_Function return Boolean
         is
            Curr_Scope : Entity_Id := FA.Analyzed_Entity;
            Prev_Scope : Entity_Id;
         begin
            loop
               Prev_Scope := Curr_Scope;
               Curr_Scope := Enclosing_Unit (Curr_Scope);

               pragma Assert (Present (Curr_Scope));

               if Ekind (Curr_Scope) = E_Protected_Type then
                  return Ekind (Prev_Scope) = E_Function;
               end if;
            end loop;
         end Is_Within_Protected_Function;

         ----------------
         -- Emit_Error --
         ----------------

         procedure Emit_Error (F : Flow_Id)
         is
         begin
            Error_Msg_Flow
              (FA       => FA,
               Msg      => Err_Desc & " cannot depend on variable input &",
               SRM_Ref  => "4.4(2)",
               N        => Err_Node,
               Severity => Error_Kind,
               F1       => Entire_Variable (F));
         end Emit_Error;

      --  Start of processing for Detect_Variable_Inputs

      begin
         for F of Variables (N) loop
            case F.Kind is
               when Direct_Mapping
                  | Record_Field
               =>
                  declare
                     Var : constant Entity_Id := Get_Direct_Mapping_Id (F);

                     use type Ada.Containers.Count_Type;
                     --  For equality of Length

                     function Is_Protected_Discriminant (F : Flow_Id)
                                                         return Boolean
                     is (Ekind (F.Component.First_Element) = E_Discriminant)
                     with Pre  => Ekind (Get_Direct_Mapping_Id (F)) =
                                    E_Protected_Type
                                  and then F.Kind = Record_Field,
                          Post => (if Is_Protected_Discriminant'Result
                                   then F.Component.Length = 1);

                  begin
                     --  We shall not get internal objects here, because
                     --  we call Get_Variables with Expand_Internal_Objects
                     --  parameter set.
                     pragma Assert (not Is_Internal (F.Node));

                     --  We emit an error if F is considered a variable, in
                     --  particular, when it is not:
                     --  * a bound
                     --  * a constant object
                     --  * a discriminant of a protected type
                     --  * a component or part of a protected type accessed
                     --    from within a protected function.

                     if not (Is_Bound (F)
                             or else
                               (Ekind (Var) = E_Protected_Type
                                and then
                                  (Is_Protected_Discriminant (F)
                                   or else
                                   Is_Within_Protected_Function))
                             or else Is_Constant_Object (Var))
                     then
                        Emit_Error (F);
                        Sane := False;
                     end if;
                  end;

               when Magic_String =>
                  if not GG_Is_Constant (F.Name) then
                     Emit_Error (F);
                     Sane := False;
                  end if;

               when others =>
                  raise Program_Error;

            end case;
         end loop;
      end Detect_Variable_Inputs;

      ------------------------------
      -- Traverse_Component_Items --
      ------------------------------

      procedure Traverse_Component_Items (L : List_Id) is
         N : Node_Id := First (L);

      begin
         while Present (N) loop
            if Nkind (N) = N_Component_Declaration then
               Check_Component_Declaration (N);
            end if;

            Next (N);
         end loop;
      end Traverse_Component_Items;

      -----------------------------
      -- Traverse_Component_List --
      -----------------------------

      procedure Traverse_Component_List (N : Node_Id) is
         Optional_Variant_Part : constant Node_Id := Variant_Part (N);

      begin
         Traverse_Component_Items (Component_Items (N));

         if Present (Optional_Variant_Part) then
            Traverse_Variant_Part (Optional_Variant_Part);
         end if;
      end Traverse_Component_List;

      -----------------------------------
      -- Traverse_Declarations_And_HSS --
      -----------------------------------

      procedure Traverse_Declarations_And_HSS (N : Node_Id) is
      begin
         Traverse_Declarations_Or_Statements (Declarations (N));
         Traverse_Handled_Statement_Sequence (Handled_Statement_Sequence (N));
      end Traverse_Declarations_And_HSS;

      -----------------------------------------
      -- Traverse_Declarations_Or_Statements --
      -----------------------------------------

      procedure Traverse_Declarations_Or_Statements (L : List_Id) is
         N : Node_Id := First (L);

      begin
         --  Loop through statements or declarations
         while Present (N) loop

            --  Check type declarations affected by SPARK RM 4.4(2)

            if Nkind (N) in N_Full_Type_Declaration
                          | N_Subtype_Declaration
                          | N_Incomplete_Type_Declaration
                          | N_Private_Type_Declaration
                          | N_Private_Extension_Declaration
            then
               Check_Type_Declaration (N);

            --  Components and discriminants are not expected here

            else
               pragma Assert (Nkind (N) not in N_Component_Declaration
                                             | N_Discriminant_Specification);
            end if;

            Traverse_Declaration_Or_Statement (N);

            Next (N);
         end loop;
      end Traverse_Declarations_Or_Statements;

      ---------------------------------------
      -- Traverse_Declaration_Or_Statement --
      ---------------------------------------

      procedure Traverse_Declaration_Or_Statement (N : Node_Id) is
      begin
         case Nkind (N) is
            when N_Protected_Body =>
               declare
                  Spec : constant Entity_Id := Corresponding_Spec (N);

               begin
                  if Entity_Body_In_SPARK (Spec) then
                     Traverse_Declarations_Or_Statements (Declarations (N));
                  end if;
               end;

            when N_Protected_Type_Declaration =>
               declare
                  Typ : constant Entity_Id := Defining_Identifier (N);

               begin
                  if Entity_Spec_In_SPARK (Typ) then

                     --  Traverse discriminants unless they are a completion of
                     --  a private type, as then they were already checked at
                     --  the type declaration.

                     if not Is_Private_Type (Etype (Typ)) then
                        Traverse_Discriminants (N);
                     end if;

                     declare
                        Def : constant Node_Id := Protected_Definition (N);

                     begin
                        Traverse_Declarations_Or_Statements
                          (Visible_Declarations (Def));

                        if Private_Spec_In_SPARK (Typ) then
                           Traverse_Component_Items
                             (Private_Declarations (Def));
                        end if;
                     end;
                  end if;
               end;

            when N_Task_Type_Declaration =>
               declare
                  Typ : constant Entity_Id := Defining_Identifier (N);

               begin
                  if Entity_Spec_In_SPARK (Typ) then

                     --  Traverse discriminants.
                     --  Note that we don't traverse them in case they are a
                     --  completion of a private type as this will have already
                     --  be checked at their declarations.

                     if not Is_Private_Type (Etype (Typ)) then
                        Traverse_Discriminants (N);
                     end if;

                     --  Traverse visible and private parts. The body part is
                     --  traversed on its own whenever we have graph for it.

                     declare
                        Def : constant Node_Id := Task_Definition (N);

                     begin
                        if Present (Def) then
                           Traverse_Declarations_Or_Statements
                             (Visible_Declarations (Def));

                           if Private_Spec_In_SPARK (Typ) then
                              Traverse_Declarations_Or_Statements
                                (Private_Declarations (Def));
                           end if;
                        end if;
                     end;
                  end if;
               end;

            when N_Full_Type_Declaration
               | N_Private_Type_Declaration
               | N_Private_Extension_Declaration
            =>
               if Comes_From_Source (N) then

                  --  Traverse discriminants

                  case Nkind (N) is
                     when N_Private_Type_Declaration =>
                        Traverse_Discriminants (N);

                     when N_Full_Type_Declaration =>
                        declare
                           Typ_Def : constant Node_Id := Type_Definition (N);

                           Optional_Component_List : Node_Id;

                        begin
                           --  We repeat effort here for private and incomplete
                           --  types, because we traverse discriminants of both
                           --  the partial declaration and its completion.
                           --  In the event that both have descriminants, the
                           --  user will see multiple flow error messages about
                           --  the same variable input, but this one line of
                           --  code is easier to maintain rather than
                           --  code that filters for each corner case.

                           Traverse_Discriminants (N);

                           --  Traverse record components
                           case Nkind (Typ_Def) is
                              when N_Record_Definition =>
                                 Optional_Component_List :=
                                   Component_List (Typ_Def);

                              when N_Derived_Type_Definition =>
                                 if Present (Record_Extension_Part (Typ_Def))
                                 then
                                    Optional_Component_List :=
                                      Component_List
                                        (Record_Extension_Part
                                           (Typ_Def));
                                 else
                                    Optional_Component_List := Empty;
                                 end if;

                              when others =>
                                 Optional_Component_List := Empty;
                           end case;

                           if Present (Optional_Component_List) then
                              Traverse_Component_List
                                (Optional_Component_List);
                           end if;

                        end;

                     --  Discriminants on derived type are not allowed in
                     --  SPARK; SPARK RM 3.7(2).

                     when N_Private_Extension_Declaration =>
                        pragma Assert (No (Discriminant_Specifications (N)));

                     when others =>
                        raise Program_Error;
                  end case;

               end if;

            when N_Block_Statement =>
               Traverse_Declarations_And_HSS (N);

            when N_If_Statement =>

               --  Traverse the statements in the THEN part

               Traverse_Declarations_Or_Statements (Then_Statements (N));

               --  Loop through ELSIF parts if present

               if Present (Elsif_Parts (N)) then
                  declare
                     Elif : Node_Id := First (Elsif_Parts (N));

                  begin
                     loop
                        Traverse_Declarations_Or_Statements
                          (Then_Statements (Elif));
                        Next (Elif);
                        exit when No (Elif);
                     end loop;
                  end;
               end if;

               --  Finally traverse the ELSE statements if present

               Traverse_Declarations_Or_Statements (Else_Statements (N));

            when N_Case_Statement =>

               --  Process case branches

               declare
                  Alt : Node_Id := First (Alternatives (N));
               begin
                  loop
                     Traverse_Declarations_Or_Statements (Statements (Alt));
                     Next (Alt);
                     exit when No (Alt);
                  end loop;
               end;

            when N_Extended_Return_Statement =>
               Traverse_Declarations_Or_Statements
                 (Return_Object_Declarations (N));
               Traverse_Handled_Statement_Sequence
                 (Handled_Statement_Sequence (N));

            when N_Loop_Statement =>
               Traverse_Declarations_Or_Statements (Statements (N));

            --  Check that an indexing expression of an indexed component or
            --  the discrete range of a slice in an object renaming
            --  declaration which renames part of that index or slice is
            --  without variable inputs.

            when N_Object_Renaming_Declaration =>
               if Comes_From_Source (N) then
                  Check_Name_Indexes_And_Slices (Name (N));
               end if;

            --  Check that that the constrained array definition of an object
            --  declaration does not contain variable inputs.

            when N_Object_Declaration =>
               Check_Constrained_Array_Definition (N);

            when others =>
               null;
         end case;
      end Traverse_Declaration_Or_Statement;

      ----------------------------
      -- Traverse_Discriminants --
      ----------------------------

      procedure Traverse_Discriminants (N : Node_Id) is
         L : constant List_Id := Discriminant_Specifications (N);
         D : Node_Id := First (L);

      begin
         while Present (D) loop
            Check_Default_Expression (D);
            Next (D);
         end loop;
      end Traverse_Discriminants;

      -----------------------------------------
      -- Traverse_Handled_Statement_Sequence --
      -----------------------------------------

      procedure Traverse_Handled_Statement_Sequence (N : Node_Id) is
         Handler : Node_Id;

      begin
         if Present (N) then
            Traverse_Declarations_Or_Statements (Statements (N));

            if Present (Exception_Handlers (N)) then
               Handler := First (Exception_Handlers (N));
               loop
                  Traverse_Declarations_Or_Statements (Statements (Handler));
                  Next (Handler);
                  exit when No (Handler);
               end loop;
            end if;
         end if;
      end Traverse_Handled_Statement_Sequence;

      ---------------------------
      -- Traverse_Variant_Part --
      ---------------------------

      procedure Traverse_Variant_Part (N : Node_Id) is
         Variant : Node_Id := First (Variants (N));

      begin
         loop
            Traverse_Component_List (Component_List (Variant));
            Next (Variant);
            exit when No (Variant);
         end loop;
      end Traverse_Variant_Part;

   --  Start of processing for Check_Expressions

   begin
      Sane := True;

      case FA.Kind is
         when Kind_Subprogram =>
            declare
               Subp_Body : constant Node_Id := Get_Body (FA.Analyzed_Entity);

            begin
               Traverse_Declarations_And_HSS (Subp_Body);

               --  If this is a user defined equality on a record type, then it
               --  shall have a Global aspect of null.

               if Is_User_Defined_Equality (FA.Spec_Entity) then
                  declare
                     Typ : constant Entity_Id :=
                       Unchecked_Full_Type
                         (Etype (First_Formal (FA.Spec_Entity)));
                     Globals : Global_Flow_Ids;
                  begin
                     if Is_Record_Type (Typ) then
                        Get_Globals (Subprogram => FA.Spec_Entity,
                                     Scope      => FA.S_Scope,
                                     Classwide  => False,
                                     Globals    => Globals);

                        if not (Globals.Proof_Ins.Is_Empty and then
                                Globals.Inputs.Is_Empty)
                        then
                           Error_Msg_Flow
                                (FA       => FA,
                                 Msg      => "user-defined equality shall " &
                                   "have a Global aspect of null",
                                 SRM_Ref  => "6.6(1)",
                                 N        => FA.Spec_Entity,
                                 Severity => Error_Kind);
                        end if;
                     end if;
                  end;
               end if;

               --  If the node is an instance of a generic then we need to
               --  check its actuals.

               if Is_Generic_Instance (FA.Analyzed_Entity) then

                  --  For subprogram instances we need to get to the
                  --  wrapper package.

                  Check_Actuals (Unique_Defining_Entity (Parent (Subp_Body)));
               end if;
            end;

         when Kind_Task =>

            --  Traverse declarations and statements in the task body. We deal
            --  with the visible and private parts of the task when analysing
            --  the enclosing subprogram/package.

            Traverse_Declarations_And_HSS (Task_Body (FA.Analyzed_Entity));

         when Kind_Package
            | Kind_Package_Body
         =>
            if Entity_Spec_In_SPARK (FA.Spec_Entity) then
               declare
                  Pkg_Spec : constant Node_Id :=
                    Package_Specification (FA.Spec_Entity);

               begin
                  Traverse_Declarations_Or_Statements
                    (Visible_Declarations (Pkg_Spec));

                  if Private_Spec_In_SPARK (FA.Spec_Entity) then
                     Traverse_Declarations_Or_Statements
                       (Private_Declarations (Pkg_Spec));

                     if Entity_Body_In_SPARK (FA.Spec_Entity) then
                        Traverse_Declarations_And_HSS
                          (Package_Body (FA.Spec_Entity));
                     end if;
                  end if;
               end;
            end if;

            --  If the node is an instance of a generic then we need to check
            --  its actuals.

            if Is_Generic_Instance (FA.Spec_Entity) then
               Check_Actuals (FA.Spec_Entity);
            end if;
      end case;

      if not Sane then
         if Gnat2Why_Args.Debug_Mode then
            Error_Msg_Flow
              (FA       => FA,
               Msg      => "flow analysis of & abandoned due to" &
                           " expressions with variable inputs",
               N        => FA.Analyzed_Entity,
               Severity => Error_Kind,
               F1       => Direct_Mapping_Id (FA.Analyzed_Entity));
         end if;
      end if;
   end Check_Expressions;

   --------------------------
   -- Check_Illegal_Writes --
   --------------------------

   procedure Check_Illegal_Writes
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean)
   is
   begin
      Sane := True;

      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : V_Attributes renames FA.Atr (V);

            F                    : Flow_Id;
            Corresp_Final_Vertex : Flow_Graphs.Vertex_Id;
            Final_Atr            : V_Attributes;

         begin
            for Var of A.Variables_Defined loop
               F := Change_Variant (Var, Normal_Use);

               if FA.Kind in Kind_Package | Kind_Package_Body
                 and then not Synthetic (F)
                 and then not FA.All_Vars.Contains (F)
               then

                  --  We have a write to a variable a package knows
                  --  nothing about. This is always an illegal update.

                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "cannot write & during elaboration of &",
                     SRM_Ref  => "7.7.1(6)",
                     N        => Error_Location (FA.PDG, FA.Atr, V),
                     Severity => High_Check_Kind,
                     Tag      => Illegal_Update,
                     F1       => Entire_Variable (Var),
                     F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                     Vertex   => V);

                  Sane := False;

               elsif not FA.All_Vars.Contains (F) then

                  --  This case is dealt with in the All_Variables_Known
                  --  sanity check.

                  null;

               elsif FA.PDG.Get_Key (V).Variant not in
                 Initial_Value | Final_Value
               then

                  --  We do know about that particular global. Now we
                  --  need to check if the update is OK.

                  Corresp_Final_Vertex :=
                    FA.PDG.Get_Vertex (Change_Variant (Var, Final_Value));
                  pragma Assert (Corresp_Final_Vertex /=
                                   Flow_Graphs.Null_Vertex);
                  Final_Atr := FA.Atr.Element (Corresp_Final_Vertex);

                  if Final_Atr.Is_Global
                    and then Final_Atr.Is_Constant
                  then
                     if FA.Kind in Kind_Package | Kind_Package_Body then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "cannot write & during" &
                                       " elaboration of &",
                           SRM_Ref  => "7.7.1(6)",
                           N        => Error_Location (FA.PDG, FA.Atr, V),
                           Severity => High_Check_Kind,
                           Tag      => Illegal_Update,
                           F1       => Var,
                           F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Vertex   => V);

                     else
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "& must be a global output of &",
                           SRM_Ref  => "6.1.4(17)",
                           N        => Error_Location (FA.PDG, FA.Atr, V),
                           Severity => High_Check_Kind,
                           F1       => Var,
                           F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Tag      => Illegal_Update,
                           Vertex   => V);
                     end if;

                     Sane := False;
                  end if;
               end if;
            end loop;
         end;
      end loop;
   end Check_Illegal_Writes;

   -------------------------------
   -- Check_All_Variables_Known --
   -------------------------------

   procedure Check_All_Variables_Known
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean)
   is
      Aspect_To_Fix : constant String :=
        (case FA.Kind is
            when Kind_Subprogram | Kind_Task =>
              (if    Present (FA.Refined_Global_N)  then "Refined_Global"
               elsif Present (FA.Refined_Depends_N) then "Refined_Depends"
               elsif Present (FA.Global_N)          then "Global"
               elsif Present (FA.Depends_N)         then "Depends"
               else                                      "Global"),

            when Kind_Package | Kind_Package_Body  =>
               "Initializes");
      --  A string representation of the aspect that needs to be corrected; the
      --  preference in choosing a contract matches the preference hardcoded in
      --  Get_Global routine. If no contract is present, then ask the user to
      --  add the Global contract, because usually it is the simplest one.

      Next_Aspect_To_Fix : constant String :=
        (case FA.Kind is
            when Kind_Subprogram | Kind_Task =>
               (if Present (FA.Global_N) and then Present (FA.Depends_N)
                then "Global and Depends"
                elsif Present (FA.Global_N)
                then "Global"
                elsif Present (FA.Depends_N)
                then "Depends"
                else ""),

            when Kind_Package | Kind_Package_Body => "");
      --  A string representation of the next aspect that needs to be
      --  corrected, i.e. this is the Global/Depends aspect if a global has
      --  been detected to be missing from a Refined_Global/Refined_Depends
      --  contract but it is not mentioned in the corresponding Global/Depends.
      --  It is both Global and Depends if the global has been detected as
      --  missing either in the Refined_Global or Refined_Depends and the
      --  subprogram is annotated with both Global and Depends contracts.

      SRM_Ref : constant String :=
        (case FA.Kind is
            when Kind_Subprogram | Kind_Task      => "6.1.4(14)",
            when Kind_Package | Kind_Package_Body => "7.1.5(11)");
      --  String representation of the violated SPARK RM rule

      function In_Abstract_Contract (FA : Flow_Analysis_Graphs; G : Flow_Id)
                                    return Boolean
      with Pre => FA.Kind in Kind_Subprogram | Kind_Task
                  and then (Present (FA.Refined_Global_N)
                            or else Present (FA.Refined_Depends_N));
      --  Returns True if G can be found in the Global or Depends contract

      --------------------------
      -- In_Abstract_Contract --
      --------------------------

      function In_Abstract_Contract (FA : Flow_Analysis_Graphs; G : Flow_Id)
                                     return Boolean
      is
      begin
         case G.Kind is
            when Magic_String =>
               return False;

            when Direct_Mapping | Record_Field =>
               declare
                  --  If the subprogram is annotated with both Global and
                  --  Depends contract, it is enough to check one of the two
                  --  cases where the global is missing from a refined contract
                  --  because if it was mentioned in one of the Global and
                  --  Depends the front-end would have already complained about
                  --  it.

                  Raw_Globals : constant Raw_Global_Nodes :=
                    (if Present (FA.Refined_Global_N)
                     then Parse_Global_Contract (FA.Analyzed_Entity,
                                                 FA.Global_N)
                     else Parse_Depends_Contract (FA.Analyzed_Entity,
                                                  FA.Depends_N));

                  use type Node_Sets.Set;

                  All_Globals : constant Node_Sets.Set :=
                    Raw_Globals.Inputs or
                    Raw_Globals.Outputs or
                    Raw_Globals.Proof_Ins;

               begin
                  return Present (Find_In (All_Globals,
                                           Get_Direct_Mapping_Id (G)));
               end;

            when others =>
               raise Program_Error;
         end case;
      end In_Abstract_Contract;

      Msg : constant String :=
          (case FA.Kind is
             when Kind_Subprogram | Kind_Task =>
                "must be listed in the " & Aspect_To_Fix & " aspect of",
             when Kind_Package | Kind_Package_Body =>
                "must be mentioned as an input of the " & Aspect_To_Fix &
                " aspect of");

   --  Start of processing for Check_All_Variables_Known

   begin
      Sane := True;

      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : V_Attributes renames FA.Atr (V);

            Variables_Referenced : constant Flow_Id_Sets.Set :=
              A.Variables_Used or A.Variables_Defined;

         begin
            for Var of Variables_Referenced loop
               case Var.Kind is

                  --  Ignore synthetic null export

                  when Synthetic_Null_Export =>
                     null;

                  --  Here we are dealing with a missing global

                  when Direct_Mapping
                     | Record_Field
                     | Magic_String
                  =>
                     if not FA.All_Vars.Contains
                       (Change_Variant (Var, Normal_Use))
                     then
                        declare
                           First_Var_Use : constant Node_Id :=
                             First_Variable_Use (FA      => FA,
                                                 Var     => Var,
                                                 Kind    => Use_Any,
                                                 Precise => False);

                           Subprogram : constant Flow_Id :=
                             Direct_Mapping_Id (FA.Analyzed_Entity);

                        begin
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      => "& " & Msg & " &",
                              SRM_Ref  => SRM_Ref,
                              N        => First_Var_Use,
                              F1       => (if Gnat2Why_Args.Flow_Advanced_Debug
                                           then Var
                                           else Entire_Variable (Var)),
                              Severity => High_Check_Kind,
                              Tag      => Global_Missing,
                              F2       => Subprogram,
                              Vertex   => V);

                           Sane := False;

                           --  If the global is missing both from the refined
                           --  contract and the abstract contract, issue a
                           --  continuation message explaining that the global
                           --  needs to be listed in the abstract contract as
                           --  well.

                           if FA.Kind in Kind_Subprogram | Kind_Task
                             and then (Present (FA.Refined_Global_N)
                                       or else Present (FA.Refined_Depends_N))
                             and then not In_Abstract_Contract (FA, Var)
                           then
                              declare
                                 Missing : constant Flow_Id :=
                                   (if Is_Constituent (Var)
                                    and then not Is_Visible (Var, FA.S_Scope)
                                    then Encapsulating_State (Var)
                                    else Entire_Variable (Var));

                              begin
                                 Error_Msg_Flow
                                   (FA           => FA,
                                    Msg          => "as a result & must be " &
                                                    "listed in the " &
                                                    Next_Aspect_To_Fix &
                                                    " of &",
                                    Severity     => High_Check_Kind,
                                    Tag          => Global_Missing,
                                    N            => First_Var_Use,
                                    F1           => Missing,
                                    F2           => Subprogram,
                                    SRM_Ref      => SRM_Ref,
                                    Continuation => True);
                              end;
                           end if;
                        end;
                     end if;

                  when Null_Value =>
                     raise Program_Error;

               end case;
            end loop;
         end;
      end loop;
   end Check_All_Variables_Known;

   ------------------------------------
   -- Check_Generated_Refined_Global --
   ------------------------------------

   procedure Check_Generated_Refined_Global
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean)
   is
      Error_Loc : constant Node_Id :=
        (if Ekind (FA.Spec_Entity) = E_Package
         then Empty
         else (if Present (FA.Global_N)
               then FA.Global_N
               else FA.Depends_N));
      --  Location for posting errors; it is either the Global (preferred) or
      --  the Depends contract, just like in Get_Global routine, which prefers
      --  the Global but uses the Depends as a fallback.

      procedure Check (Generated :     Flow_Id_Sets.Set;
                       User      :     Flow_Id_Sets.Set;
                       Missing   : out Flow_Id_Sets.Set;
                       Unused    : out Flow_Id_Sets.Set)
      with Post => Missing.Is_Subset (Of_Set => Generated) and then
                   Unused.Is_Subset (Of_Set => User);
      --  Compute missing and unused user globals based on generated and those
      --  provided by the user.

      procedure Error_Msg (Msg : String; Severity : Msg_Severity; F : Flow_Id);
      --  Wrapper to simplify reporting errors about missing and unused globals

      -----------
      -- Check --
      -----------

      procedure Check (Generated :     Flow_Id_Sets.Set;
                       User      :     Flow_Id_Sets.Set;
                       Missing   : out Flow_Id_Sets.Set;
                       Unused    : out Flow_Id_Sets.Set)
      is
      begin
         Missing := Flow_Id_Sets.Empty_Set;
         Unused  := User;

         for G of Generated loop
            declare
               U : constant Flow_Id := Find_In (User, G);

            begin
               if Present (U) then
                  Unused.Exclude (U);
               else
                  Missing.Insert (G);
               end if;
            end;
         end loop;
      end Check;

      ---------------
      -- Error_Msg --
      ---------------

      procedure Error_Msg (Msg : String; Severity : Msg_Severity; F : Flow_Id)
      is
      begin
         Sane := False;

         Error_Msg_Flow
           (FA       => FA,
            Msg      => Msg,
            N        => Error_Loc,
            Severity => Severity,
            F1       => F,
            F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
            Tag      => Global_Missing);
      end Error_Msg;

      --  Local variables

      Raw_Globals : Raw_Global_Nodes;
      User_Global : Global_Flow_Ids;
      --  Global contract provided by the user

      Generated_Refined_Global : Global_Flow_Ids;
      --  Refined_Global contract generated by the flow analysis

      Generated_Global : Global_Flow_Ids;
      --  Generated Global contract up-projected to the spec scope

      Unused_Inputs    : Flow_Id_Sets.Set;
      Unused_Outputs   : Flow_Id_Sets.Set;
      Unused_Proof_Ins : Flow_Id_Sets.Set;

      Missing_Inputs    : Flow_Id_Sets.Set;
      Missing_Outputs   : Flow_Id_Sets.Set;
      Missing_Proof_Ins : Flow_Id_Sets.Set;
      --  Unused and missing user globals; Input/Output/Proof_In are stored
      --  in individual containers to not worry about the type predicate of
      --  Global_Flow_Ids.

   --  Start of processing for Check_Generated_Refined_Global

   begin
      Sane := True;

      --  Only apply this check to entities with user supplied abstract
      --  Global/Depends and generated Refined_Global.

      if not (Ekind (FA.Spec_Entity) /= E_Package
                and then Has_User_Supplied_Globals (FA.Spec_Entity)
                and then FA.Is_Generative)
      then
         return;
      end if;

      --  Read the user-written Global or Depends

      if Present (FA.Global_N) then
         Raw_Globals := Parse_Global_Contract (Subprogram  => FA.Spec_Entity,
                                               Global_Node => FA.Global_N);

      elsif Present (FA.Depends_N) then
         Raw_Globals := Parse_Depends_Contract (Subprogram   => FA.Spec_Entity,
                                                Depends_Node => FA.Depends_N);

      else
         pragma Assert (Is_Pure (FA.Spec_Entity));
      end if;

      --  Convert user-globals from Entity_Ids to Flow_Ids

      User_Global :=
        (Proof_Ins => To_Flow_Id_Set (Raw_Globals.Proof_Ins, In_View),
         Inputs    => To_Flow_Id_Set (Raw_Globals.Inputs,    In_View),
         Outputs   => To_Flow_Id_Set (Raw_Globals.Outputs,   Out_View));

      --  Read the generated Refined_Global

      Get_Globals (Subprogram => FA.Analyzed_Entity,
                   Scope      => FA.B_Scope,
                   Classwide  => False,
                   Globals    => Generated_Refined_Global);

      --  Up project actual globals

      Up_Project (Generated_Refined_Global, Generated_Global, FA.S_Scope);

      --  Detect inconsistent globals

      Check (Generated => Generated_Global.Inputs,
             User      => User_Global.Inputs,
             Missing   => Missing_Inputs,
             Unused    => Unused_Inputs);

      Check (Generated => Generated_Global.Outputs,
             User      => User_Global.Outputs,
             Missing   => Missing_Outputs,
             Unused    => Unused_Outputs);

      Check (Generated => Generated_Global.Proof_Ins,
             User      => User_Global.Proof_Ins,
             Missing   => Missing_Proof_Ins,
             Unused    => Unused_Proof_Ins);

      --  Flag missing user globals

      for Missing of Missing_Inputs loop
         Error_Msg
           (Msg      => "& must be a global " &
                        (if Present
                           (Find_In (User_Global.Outputs,
                                     Change_Variant (Missing, Out_View)))
                         then "In_Out of &"
                         else "Input of &"),
            Severity => Medium_Check_Kind,
            F        => Missing);
      end loop;

      for Missing of Missing_Outputs loop
         Error_Msg
           (Msg      => "& must be a global " &
                        (if Present
                           (Find_In (User_Global.Inputs,
                                     Change_Variant (Missing, In_View)))
                         then "In_Out of &"
                         else "Output of &"),
            Severity => High_Check_Kind,
            F        => Missing);
      end loop;

      for Missing of Missing_Proof_Ins loop
         Error_Msg
           (Msg      => "& must be a global Proof_In of &",
            Severity => Medium_Check_Kind,
            F        => Missing);

      end loop;

      --  Flag extra user globals

      for Unused of Unused_Inputs loop
         if not Is_Dummy_Abstract_State (Unused, FA.B_Scope) then
            Error_Msg
              (Msg      => "global Input & of & not read",
               Severity => Low_Check_Kind,
               F        => Unused);
         end if;
      end loop;

      for Unused of Unused_Outputs loop
         if not Is_Dummy_Abstract_State (Unused, FA.B_Scope) then
            Error_Msg
              (Msg      => "global Output & of & not written",
               Severity => Error_Kind,
               F        => Unused);
         end if;
      end loop;

      for Unused of Unused_Proof_Ins loop
         if not Is_Dummy_Abstract_State (Unused, FA.B_Scope) then
            Error_Msg
              (Msg      => "global Proof_In & of & not read",
               Severity => Error_Kind,
               F        => Unused);
         end if;
      end loop;
   end Check_Generated_Refined_Global;

   -----------------------------------------------
   -- Check_Side_Effects_In_Protected_Functions --
   -----------------------------------------------

   procedure Check_Side_Effects_In_Protected_Functions
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean)
   is
   begin
      Sane := True;

      if Ekind (FA.Spec_Entity) = E_Function
        and then Ekind (Scope (FA.Spec_Entity)) = E_Protected_Type
      then
         for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
            declare
               Atr : V_Attributes renames FA.Atr (V);

            begin
               if Atr.Is_Program_Node then
                  for Var of Atr.Variables_Used loop
                     if Belongs_To_Concurrent_Type (Var)
                       and then Has_Effective_Reads (Var)
                     then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "protected function with effective " &
                                       "reads & is not allowed in SPARK",
                           N        => (if Present (Atr.Error_Location)
                                        then Atr.Error_Location
                                        else FA.Spec_Entity),
                           F1       => Var,
                           Severity => Error_Kind,
                           Tag      => Side_Effects);
                        --  ??? the Atr.Error_Location should be always present
                        --  (which should be enforced by the graph building
                        --  API); we check it only to be on the safe side.
                        Sane := False;
                     end if;
                  end loop;
               end if;
            end;
         end loop;
      end if;
   end Check_Side_Effects_In_Protected_Functions;

end Flow.Analysis.Sanity;
