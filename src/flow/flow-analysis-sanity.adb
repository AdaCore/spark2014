------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . A N A L Y S I S . S A N I T Y                  --
--                                                                          --
--                                B o d y                                   --
--                                                                          --
--              Copyright (C) 2013-2025, Capgemini Engineering              --
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

with Atree;                          use Atree;
with Checked_Types;                  use Checked_Types;
with Errout_Wrapper;                 use Errout_Wrapper;
with Flow_Classwide;
with Flow_Error_Messages;            use Flow_Error_Messages;
with Flow_Utility;                   use Flow_Utility;
with Flow_Refinement;                use Flow_Refinement;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Gnat2Why_Args;
with Namet;                          use Namet;
with Nlists;                         use Nlists;
with Sem_Aux;                        use Sem_Aux;
with Sem_Util;                       use Sem_Util;
with Sinfo.Utils;                    use Sinfo.Utils;
with Sinput;                         use Sinput;
with Snames;                         use Snames;
with SPARK_Definition;               use SPARK_Definition;
with SPARK_Util.Subprograms;         use SPARK_Util.Subprograms;
with SPARK_Util.Types;               use SPARK_Util.Types;
with SPARK_Util;                     use SPARK_Util;
with VC_Kinds;                       use VC_Kinds;

package body Flow.Analysis.Sanity is

   use type Flow_Graphs.Vertex_Id;
   use type Flow_Id_Sets.Set;

   ---------------------------------
   -- Check_Function_Side_Effects --
   ---------------------------------

   procedure Check_Function_Side_Effects
     (FA : in out Flow_Analysis_Graphs; Sane : out Boolean)
   is
      Globals : Global_Flow_Ids;

   begin
      Sane := True;

      if Ekind (FA.Spec_Entity) = E_Function
        and then not Is_Function_With_Side_Effects (FA.Spec_Entity)
      then

         Get_Globals
           (Subprogram => FA.Spec_Entity,
            Scope      => FA.B_Scope,
            Classwide  => False,
            Globals    => Globals);

         if not Globals.Outputs.Is_Empty then

            Sane := False;

            for G of Globals.Outputs loop
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      =>
                    "function with output global & "
                    & "is not allowed in SPARK",
                  N        => FA.Spec_Entity,
                  F1       => G,
                  Severity => Error_Kind,
                  Tag      => Side_Effects);
            end loop;

            pragma Annotate (Xcov, Exempt_On, "Debugging code");
            if Gnat2Why_Args.Debug_Mode then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      =>
                    "flow analysis of & abandoned due to "
                    & "function with side effects",
                  N        => FA.Spec_Entity,
                  Severity => Error_Kind,
                  F1       => Direct_Mapping_Id (FA.Spec_Entity));
            end if;
            pragma Annotate (Xcov, Exempt_Off);

         end if;
      end if;
   end Check_Function_Side_Effects;

   -----------------------
   -- Check_Expressions --
   -----------------------

   procedure Check_Expressions
     (FA : in out Flow_Analysis_Graphs; Sane : out Boolean)
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

      procedure Check_Component_Definition (N : Node_Id)
      with Pre => Nkind (N) = N_Component_Definition;
      --  Check array/record/protected component definition

      procedure Check_Default_Expression (N : Node_Id)
      with
        Pre =>
          Nkind (N) in N_Component_Declaration | N_Discriminant_Specification;
      --  Check the default expression of component or discriminant, if
      --  present, i.e. SPARK RM 4.4(2) rules about:
      --  * the default expression of a component declaration
      --  * the default expression of a discriminant_specification

      function Check_Name_Dereference (N : Node_Id) return Traverse_Result;
      --  Check SPARK RM 4.4(2) rule about:
      --  * a dereference in an object renaming declaration which renames
      --    part of that dereference.

      procedure Check_Name_Dereferences is new
        Traverse_More_Proc (Check_Name_Dereference);

      function Check_Name_Index_And_Slice (N : Node_Id) return Traverse_Result;
      --  Check SPARK RM 4.4(2) rule about:
      --  * an indexing expression of an indexed component or the discrete
      --    range of a slice in an object renaming declaration which renames
      --    part of that index or slice.

      procedure Check_Name_Indexes_And_Slices is new
        Traverse_More_Proc (Check_Name_Index_And_Slice);

      procedure Check_Subtype_Constraints (N : Node_Id);
      --  Check that subtype constraints do not have variable inputs

      procedure Check_Subtype_Indication (N : Node_Id);
      --  Check a subtype indication (roughly speaking, a node where a type
      --  name is expected).

      procedure Check_Type_Aspects (N : Node_Id)
      with
        Pre =>
          Nkind (N)
          in N_Full_Type_Declaration
           | N_Subtype_Declaration
           | N_Incomplete_Type_Declaration
           | N_Private_Type_Declaration
           | N_Private_Extension_Declaration;
      --  Enforce SPARK RM 4.4(2) by checking:
      --  * a Dynamic_Predicate aspect specification
      --  * a Type_Invariant aspect specification

      procedure Check_Constrained_Array_Definition (Typ_Def : Node_Id)
      with Pre => Nkind (Typ_Def) = N_Constrained_Array_Definition;
      --  Check if Typ_Def is a constrained array definition with variable
      --  inputs, as per SPARK RM 4.4(2).

      procedure Detect_Variable_Inputs
        (N : Node_Id; Err_Desc : String; Cont : String := "")
      with Pre => Nkind (N) in N_Subexpr;
      --  Emit error for any object referenced within N which does NOT denote
      --  a constant, a bound or a discriminant (of an enclosing concurrent
      --  type).

      procedure Traverse_Declarations_And_HSS (N : Node_Id);
      procedure Traverse_Declarations_Or_Statements (L : List_Id);
      procedure Traverse_Declaration_Or_Statement (N : Node_Id);
      procedure Traverse_Handled_Statement_Sequence (N : Node_Id);
      --  Traverse declarations and statements

      procedure Traverse_Component_List (N : Node_Id)
      with Pre => Nkind (N) = N_Component_List;
      procedure Traverse_Component_Items (L : List_Id);
      procedure Traverse_Discriminants (N : Node_Id);
      procedure Traverse_Variant_Part (N : Node_Id)
      with Pre => Nkind (N) = N_Variant_Part;
      --  Traversals for components and discriminants
      --
      --  Note: discriminants appear in various nodes; components appear in
      --  protected types and record types (both as immediate children or in
      --  arbitrarily nested variant parts).

      function Variables (N : Node_Id) return Flow_Id_Sets.Set
      is (Get_All_Variables
            (N                       => N,
             Scope                   => FA.B_Scope,
             Target_Name             => Null_Flow_Id,
             Use_Computed_Globals    => True,
             Expand_Internal_Objects =>
             --  Do not expand constants in inlined bodies,
             --  as this leads to spurious errors. Any
             --  relevant errors related to variable input
             --  are reported on the non-inlined code.
               not Comes_From_Inlined_Body (Sloc (N))));
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
                     Err_Desc => "actual for formal object with mode in");

               elsif Nkind (Decl) = N_Object_Renaming_Declaration
                 and then Present (Corresponding_Generic_Association (Decl))
               then
                  Check_Name_Dereferences (Name (Decl));
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
         Check_Component_Definition (Component_Definition (N));
         Check_Default_Expression (N);
      end Check_Component_Declaration;

      --------------------------------
      -- Check_Component_Definition --
      --------------------------------

      procedure Check_Component_Definition (N : Node_Id) is
      begin
         --  Component definition is given either as a subtype_indication
         --  (whose constraints need to be checked) or as an access_definition
         --  (which cannot depend on variable inputs).

         pragma
           Assert
             (Present (Subtype_Indication (N))
                xor Present (Access_Definition (N)));

         if Present (Subtype_Indication (N)) then
            Check_Subtype_Indication (Subtype_Indication (N));
         end if;

      end Check_Component_Definition;

      ------------------------------
      -- Check_Default_Expression --
      ------------------------------

      procedure Check_Default_Expression (N : Node_Id) is
         Default_Expression : constant Node_Id := Expression (N);

      begin
         if Present (Default_Expression) then
            Detect_Variable_Inputs
              (N => Default_Expression, Err_Desc => "default initialization");
         end if;
      end Check_Default_Expression;

      ----------------------------
      -- Check_Name_Dereference --
      ----------------------------

      function Check_Name_Dereference (N : Node_Id) return Traverse_Result is
      begin
         if Nkind (N) = N_Explicit_Dereference then
            declare
               Pref : constant Node_Id := Prefix (N);

            begin
               --  Skip the check if Pref is a constant, as constants of an
               --  access-to-variable type are not considered to have variable
               --  inputs in this case.

               if Nkind (Pref) in N_Identifier | N_Expanded_Name
                 and then Ekind (Entity (Pref)) in E_Constant | E_In_Parameter
               then
                  null;
               else
                  Detect_Variable_Inputs
                    (N        => Pref,
                     Err_Desc => "renamed dereference",
                     Cont     =>
                       "introduce a constant of an anonymous "
                       & "access type for the prefix of the dereference");
               end if;
            end;

            --  Detecting variable inputs in the prefix will detect them in
            --  nested prefixes too, so don't traverse the child nodes.

            return Skip;

         --  Keep searching in sibling expressions

         else
            return OK;
         end if;
      end Check_Name_Dereference;

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
                       (N => Expr, Err_Desc => "renamed index");
                     Next (Expr);
                     exit when No (Expr);
                  end loop;
               end;

            when N_Slice =>
               declare
                  R : constant Node_Id := Discrete_Range (N);
               begin
                  Detect_Variable_Inputs
                    (N        =>
                       (if Nkind (R) = N_Subtype_Indication
                        then Range_Expression (Constraint (R))
                        else R),
                     Err_Desc => "renamed slice");
               end;

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
                    (N => Lo, Err_Desc => "subtype constraint");

                  Detect_Variable_Inputs
                    (N => Hi, Err_Desc => "subtype constraint");
               end;

            when N_Range_Constraint =>
               declare
                  Range_Expr : constant Node_Id := Range_Expression (N);

                  Lo : constant Node_Id := Low_Bound (Range_Expr);
                  Hi : constant Node_Id := High_Bound (Range_Expr);

               begin
                  Detect_Variable_Inputs
                    (N => Lo, Err_Desc => "subtype constraint");

                  Detect_Variable_Inputs
                    (N => Hi, Err_Desc => "subtype constraint");
               end;

            when N_Index_Or_Discriminant_Constraint =>
               declare
                  Constr : Node_Id := First (Constraints (N));

               begin
                  loop
                     case Nkind (Constr) is
                        when N_Subtype_Indication =>
                           Check_Subtype_Constraints (Constraint (Constr));

                        when N_Range =>
                           Check_Subtype_Constraints (Constr);

                        when N_Discriminant_Association =>
                           Detect_Variable_Inputs
                             (N        => Expression (Constr),
                              Err_Desc => "subtype constraint");

                        when others =>
                           if Is_Entity_Name (Constr)
                             and then Is_Type (Entity (Constr))
                           then
                              pragma
                                Assert (Is_Discrete_Type (Entity (Constr)));
                           else
                              Detect_Variable_Inputs
                                (N        => Constr,
                                 Err_Desc => "subtype constraint");
                           end if;
                     end case;

                     Next (Constr);
                     exit when No (Constr);
                  end loop;
               end;

            when N_Delta_Constraint | N_Digits_Constraint =>

               --  Ada LRM requires these constraints to be static, so no
               --  further action required here.

               null;

            when others =>
               raise Program_Error;
         end case;
      end Check_Subtype_Constraints;

      ------------------------------
      -- Check_Subtype_Indication --
      ------------------------------

      procedure Check_Subtype_Indication (N : Node_Id) is
      begin
         case Nkind (N) is
            when N_Access_Definition =>
               pragma
                 Assert
                   (if Present (Subtype_Mark (N))
                      then Is_Type (Entity (Subtype_Mark (N)))
                      else Present (Access_To_Subprogram_Definition (N)));

            when N_Attribute_Reference =>
               pragma Assert (Is_Type_Attribute_Name (Attribute_Name (N)));

            when N_Expanded_Name | N_Identifier =>
               pragma Assert (Is_Type (Entity (N)));

            when N_Subtype_Indication =>
               Check_Subtype_Constraints (Constraint (N));

            when N_Constrained_Array_Definition =>
               Check_Constrained_Array_Definition (N);

            when N_Unconstrained_Array_Definition =>
               null;

            when others =>
               raise Program_Error;
         end case;
      end Check_Subtype_Indication;

      ----------------------------------------
      -- Check_Constrained_Array_Definition --
      ----------------------------------------

      procedure Check_Constrained_Array_Definition (Typ_Def : Node_Id) is
         DSD : Node_Id := First (Discrete_Subtype_Definitions (Typ_Def));
      begin
         loop
            case Nkind (DSD) is
               when N_Range =>
                  Check_Subtype_Constraints (DSD);

               when N_Subtype_Indication =>
                  pragma
                    Assert (Nkind (Constraint (DSD)) = N_Range_Constraint);
                  Check_Subtype_Constraints (Constraint (DSD));

               when N_Identifier | N_Expanded_Name =>
                  pragma Assert (Is_Discrete_Type (Entity (DSD)));

               when others =>
                  raise Program_Error;
            end case;

            Next (DSD);

            exit when No (DSD);
         end loop;
      end Check_Constrained_Array_Definition;

      ------------------------
      -- Check_Type_Aspects --
      ------------------------

      procedure Check_Type_Aspects (N : Node_Id) is
         Typ : constant Type_Kind_Id := Defining_Identifier (N);
         Rep : Node_Id := First_Rep_Item (Typ);

      begin
         --  Check that the type predicate expression, if present, does not
         --  have variable inputs and does not reference potentially
         --  nonreturning functions. We don't use Has_Predicates because in
         --  case of a type with a completion will return True both for the
         --  type declaration and the completion and we don't want to have
         --  duplicate checks.

         Find_Predicate_Item (Typ, Rep);

         if Present (Rep) then
            declare
               Expr : constant Node_Id :=
                 Get_Expr_From_Return_Only_Func (Predicate_Function (Typ));

               Funcalls  : Call_Sets.Set;
               Indcalls  : Node_Sets.Set;
               Proofdeps : Node_Sets.Set;
               Unused    : Tasking_Info;

            begin

               --  Check that the type predicate expression does not have
               --  variable inputs.

               Detect_Variable_Inputs (N => Expr, Err_Desc => "predicate");

               Pick_Generated_Info
                 (Expr,
                  Scop               => Get_Flow_Scope (Expr),
                  Function_Calls     => Funcalls,
                  Indirect_Calls     => Indcalls,
                  Proof_Dependencies => Proofdeps,
                  Tasking            => Unused,
                  Generating_Globals => False);

               --  Check that the type predicate expression has no calls via
               --  access-to-subprogram or dispatching calls. If the type
               --  is an access-to-subprogram that references itself in its
               --  predicate, a check message is also emitted.

               for SC of Funcalls loop
                  if Ekind (SC.E) = E_Subprogram_Type then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      =>
                          "call via access-to-subprogram "
                          & "in the predicate of & might not terminate",
                        Severity => High_Check_Kind,
                        Tag      => Subprogram_Termination,
                        N        => Expr,
                        F1       => Direct_Mapping_Id (Typ),
                        SRM_Ref  => "3.2.4(4)");

                  elsif Nkind (SC.N) in N_Subprogram_Call
                    and then Flow_Classwide.Is_Dispatching_Call (SC.N)
                  then
                     Error_Msg_Flow
                       (FA          => FA,
                        Msg         =>
                          "dispatching call "
                          & "in the predicate of & might not terminate",
                        Explanation => "call could hide recursive calls",
                        Severity    => High_Check_Kind,
                        Tag         => Subprogram_Termination,
                        N           => Expr,
                        F1          => Direct_Mapping_Id (Typ),
                        SRM_Ref     => "3.2.4(4)");
                  end if;
               end loop;
            end;
         end if;

         --  Check that the type invariant expression, if present, does not
         --  have variable inputs and does not reference potentially
         --  nonreturning functions. Has_Invariants_In_SPARK operates on the
         --  public view of a type and therefore we call it on private type
         --  declarations or extensions.

         if Nkind (N)
            in N_Private_Type_Declaration | N_Private_Extension_Declaration
           and then Has_Invariants_In_SPARK (Typ)
         then
            for Expr of
              Get_Exprs_From_Check_Only_Proc (Invariant_Procedure (Typ))
            loop
               declare
                  Funcalls  : Call_Sets.Set;
                  Indcalls  : Node_Sets.Set;
                  Proofdeps : Node_Sets.Set;
                  Unused    : Tasking_Info;

               begin
                  --  Check 7.3.2(3) [which is really 4.4(2)] (no variable
                  --  inputs).

                  Detect_Variable_Inputs (N => Expr, Err_Desc => "invariant");

                  Pick_Generated_Info
                    (Expr,
                     Scop               => Get_Flow_Scope (Expr),
                     Function_Calls     => Funcalls,
                     Indirect_Calls     => Indcalls,
                     Proof_Dependencies => Proofdeps,
                     Tasking            => Unused,
                     Generating_Globals => False);

                  for SC of Funcalls loop

                     --  Check 7.3.2(11) (no calls via access-to-subprogram)

                     if Ekind (SC.E) = E_Subprogram_Type then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      =>
                             "call via access-to-subprogram "
                             & "in the invariant of & might not terminate",
                           Severity => High_Check_Kind,
                           Tag      => Subprogram_Termination,
                           N        => Expr,
                           F1       => Direct_Mapping_Id (Typ),
                           SRM_Ref  => "7.3.2(11)");

                     --  Check 7.3.2(11) (no dispatching calls)

                     elsif Nkind (SC.N) in N_Subprogram_Call
                       and then Flow_Classwide.Is_Dispatching_Call (SC.N)
                     then
                        Error_Msg_Flow
                          (FA          => FA,
                           Msg         =>
                             "dispatching call "
                             & "in the invariant of & might not terminate",
                           Explanation => "call could hide recursive calls",
                           Severity    => High_Check_Kind,
                           Tag         => Subprogram_Termination,
                           N           => Expr,
                           F1          => Direct_Mapping_Id (Typ),
                           SRM_Ref     => "7.3.2(11)");

                     --  Check 7.3.2(5) (no calls to boundary subprograms)

                     elsif Is_Boundary_Subprogram_For_Type (SC.E, Typ) then

                        --  Check formal parameters

                        declare
                           Formal : Opt_Formal_Kind_Id := First_Formal (SC.E);
                        begin
                           while Present (Formal) loop
                              if Has_Subcomponents_Of_Type
                                   (Etype (Formal), Typ)
                              then
                                 Error_Msg_Flow
                                   (FA       => FA,
                                    Msg      =>
                                      "cannot call boundary subprogram & "
                                      & "for type & in its own invariant",
                                    Severity => High_Check_Kind,
                                    Tag      => Call_In_Type_Invariant,
                                    N        => Expr,
                                    F1       => Direct_Mapping_Id (SC.E),
                                    F2       => Direct_Mapping_Id (Typ),
                                    SRM_Ref  => "7.3.2(5)");
                                 exit;
                              end if;
                              Next_Formal (Formal);
                           end loop;
                        end;

                        --  Check global parameters

                        declare
                           Inputs, Outputs : Flow_Id_Sets.Set;
                        begin
                           Get_Proof_Globals
                             (Subprogram      => SC.E,
                              Reads           => Inputs,
                              Writes          => Outputs,
                              Erase_Constants => False);

                           --  Functions will be checked for side effects, so
                           --  here we only examine inputs and ignore outputs.

                           for Input of Inputs loop
                              if Input.Kind = Direct_Mapping
                                and then Has_Subcomponents_Of_Type
                                           (Etype
                                              (Get_Direct_Mapping_Id (Input)),
                                            Typ)
                              then
                                 Error_Msg_Flow
                                   (FA       => FA,
                                    Msg      =>
                                      "cannot call boundary subprogram & "
                                      & "for type & with global & "
                                      & "in its own invariant",
                                    Severity => High_Check_Kind,
                                    Tag      => Call_In_Type_Invariant,
                                    N        => Expr,
                                    F1       => Direct_Mapping_Id (SC.E),
                                    F2       => Direct_Mapping_Id (Typ),
                                    F3       => Input,
                                    SRM_Ref  => "7.3.2(5)");

                              --  If we don't have the Entity_Id of a global,
                              --  then we don't have its Etype either. Force
                              --  the user to provide an explicit Global
                              --  contract.

                              elsif Input.Kind = Magic_String then
                                 Error_Msg_Flow
                                   (FA       => FA,
                                    Msg      =>
                                      "cannot call boundary subprogram & "
                                      & "for type & with implicit global & "
                                      & "in its own invariant",
                                    Severity => High_Check_Kind,
                                    Tag      => Call_In_Type_Invariant,
                                    N        => Expr,
                                    F1       => Direct_Mapping_Id (SC.E),
                                    F2       => Direct_Mapping_Id (Typ),
                                    F3       => Input,
                                    SRM_Ref  => "7.3.2(5)");
                              end if;
                           end loop;
                        end;
                     end if;
                  end loop;
               end;
            end loop;
         end if;
      end Check_Type_Aspects;

      ---------------------------
      -- Detect_Variable_Inputs --
      ---------------------------

      procedure Detect_Variable_Inputs
        (N : Node_Id; Err_Desc : String; Cont : String := "")
      is
         function Is_Within_Protected_Function return Boolean;
         --  Returns True if we are inside a protected function, False if
         --  inside a protected procedure or entry, and crashes otherwise.

         procedure Emit_Error (F : Flow_Id);

         ----------------------------------
         -- Is_Within_Protected_Function --
         ----------------------------------

         function Is_Within_Protected_Function return Boolean is
            Curr_Scope : Unit_Kind_Id := FA.Spec_Entity;
            Prev_Scope : Unit_Kind_Id;
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

         procedure Emit_Error (F : Flow_Id) is
            Continuation : constant String :=
              (if Cont'Length > 0
               then Cont
               else
                 "use instead a constant initialized to the "
                 & "expression with variable input");
         begin
            Error_Msg_Flow
              (FA            => FA,
               Msg           =>
                 Err_Desc & " cannot depend on variable input &",
               Explain_Code  => EC_Variable_Input_In_Expression,
               N             => N,
               Severity      => Error_Kind,
               F1            => Entire_Variable (F),
               Continuations => [Create (Continuation)]);
            Sane := False;
         end Emit_Error;

         --  Start of processing for Detect_Variable_Inputs

      begin
         for F of Variables (N) loop
            case F.Kind is
               when Direct_Mapping | Record_Field =>
                  declare
                     Var : constant Entity_Id := Get_Direct_Mapping_Id (F);

                     use type Ada.Containers.Count_Type;
                     --  For equality of Length

                     function Is_Protected_Discriminant
                       (F : Flow_Id) return Boolean
                     is (Ekind (F.Component.First_Element) = E_Discriminant)
                     with
                       Pre  =>
                         Ekind (Get_Direct_Mapping_Id (F)) = E_Protected_Type
                         and then F.Kind = Record_Field,
                       Post =>
                         (if Is_Protected_Discriminant'Result
                          then F.Component.Length = 1);

                     function Is_Record_Discriminant
                       (F : Flow_Id) return Boolean
                     is (F.Kind = Record_Field
                         and then Ekind (Get_Direct_Mapping_Id (F))
                                  in Record_Kind | Private_Kind
                         and then Ekind (F.Component.First_Element)
                                  = E_Discriminant)
                     with
                       Post =>
                         (if Is_Record_Discriminant'Result
                          then F.Component.Length = 1);

                  begin
                     --  We call Get_Variables with Expand_Internal_Objects
                     --  parameter set. The only times we should get
                     --  an internal object here are for type discriminant
                     --  constructs and deferred constants.
                     pragma
                       Assert
                         (if Is_Internal (Var)
                            then
                              (Is_Type (Var) and then Is_Discriminant (F))
                              or else (Ekind (Var) = E_Constant
                                       and then Has_Completion (Var)));

                     --  We emit an error if F is considered a variable, in
                     --  particular, when it is not:
                     --  * a bound
                     --  * a constant object
                     --  * a record discriminant
                     --  * a discriminant of a protected type
                     --  * a component or part of a protected type accessed
                     --    from within a protected function.

                     --  The frontend introduces a variable for the current
                     --  instance in a predicate, which should not lead to an
                     --  error here.

                     --  disable formatting for deeply nested condition
                     --!format off
                     if not (Is_Bound (F)
                             or else (Is_Constant_Object (Var)
                                      and then (not Is_Access_Variable
                                                      (Etype (Var))
                                                or else not Comes_From_Source
                                                              (Var)))
                             or else Is_Record_Discriminant (F)
                             or else (Ekind (Var) = E_Protected_Type
                                      and then
                                       (Is_Protected_Discriminant (F)
                                        or else Is_Within_Protected_Function)))
                     --!format on
                     then
                        Emit_Error (F);
                     end if;
                  end;

               when Magic_String =>
                  if not GG_Is_Constant (F.Name) then
                     Emit_Error (F);
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
         while Present (N) loop
            Traverse_Declaration_Or_Statement (N);
            Next (N);
         end loop;
      end Traverse_Declarations_Or_Statements;

      ---------------------------------------
      -- Traverse_Declaration_Or_Statement --
      ---------------------------------------

      procedure Traverse_Declaration_Or_Statement (N : Node_Id) is
      begin
         --  Emit precise error location in case of a crash
         Current_Error_Node := N;

         --  Check type declarations affected by SPARK RM 4.4(2)

         if Nkind (N)
            in N_Full_Type_Declaration
             | N_Subtype_Declaration
             | N_Incomplete_Type_Declaration
             | N_Private_Type_Declaration
             | N_Private_Extension_Declaration
         then
            Check_Type_Aspects (N);
         end if;

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

            when N_Full_Type_Declaration =>
               if Comes_From_Source (N) then
                  declare
                     Typ_Def : constant Node_Id := Type_Definition (N);

                     Optional_Component_List : Node_Id;

                  begin
                     --  We repeat effort here for private and incomplete
                     --  types, because we traverse discriminants of both the
                     --  partial declaration and its completion. When both have
                     --  descriminants, we will emit multiple messages about
                     --  the same variable input, but this is easier to
                     --  maintain rather than filtering for each corner case.

                     Traverse_Discriminants (N);

                     case Nkind (Typ_Def) is
                        when N_Access_To_Object_Definition =>
                           Check_Subtype_Indication
                             (Subtype_Indication (Typ_Def));

                           Optional_Component_List := Empty;

                        when N_Record_Definition =>
                           Optional_Component_List := Component_List (Typ_Def);

                           if Present (Optional_Component_List) then
                              Traverse_Component_List
                                (Optional_Component_List);
                           end if;

                        when N_Derived_Type_Definition =>
                           Check_Subtype_Indication
                             (Subtype_Indication (Typ_Def));

                           if Present (Record_Extension_Part (Typ_Def)) then
                              Optional_Component_List :=
                                Component_List
                                  (Record_Extension_Part (Typ_Def));

                              if Present (Optional_Component_List) then
                                 Traverse_Component_List
                                   (Optional_Component_List);
                              end if;
                           end if;

                        when N_Array_Type_Definition =>
                           Check_Subtype_Indication (Typ_Def);
                           Check_Component_Definition
                             (Component_Definition (Typ_Def));

                        --  The following are either enumeration literals,
                        --  static expressions, or access to subprogram
                        --  definitions.

                        when N_Access_Function_Definition
                           | N_Access_Procedure_Definition
                           | N_Decimal_Fixed_Point_Definition
                           | N_Enumeration_Type_Definition
                           | N_Floating_Point_Definition
                           | N_Modular_Type_Definition
                           | N_Ordinary_Fixed_Point_Definition
                           | N_Signed_Integer_Type_Definition
                        =>
                           null;

                        when others =>
                           raise Program_Error;
                     end case;
                  end;
               end if;

            when N_Private_Type_Declaration =>
               Traverse_Discriminants (N);

            when N_Private_Extension_Declaration =>
               --  Discriminants on derived type are not allowed in SPARK;
               --  SPARK RM 3.7(2).

               pragma Assert (No (Discriminant_Specifications (N)));
               Check_Subtype_Indication (Subtype_Indication (N));

            when N_Subtype_Declaration =>
               --  Completions of incomplete types are rewritten from full type
               --  declarations to subtypes that do not come from source.

               if Comes_From_Source (N) or else Is_Rewrite_Substitution (N)
               then
                  Check_Subtype_Indication (Subtype_Indication (N));
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

               --  Process case alterantives

               declare
                  Alt : Node_Id := First_Non_Pragma (Alternatives (N));
               begin
                  loop
                     Traverse_Declarations_Or_Statements (Statements (Alt));
                     Next_Non_Pragma (Alt);
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

            when N_Object_Renaming_Declaration =>

               if Comes_From_Source (N) then
                  --  The checks below apply to generic in-out parameters which
                  --  are transformed into renamings by GNAT (and SPARK RM rule
                  --  makes provisions for such checking), but we check this
                  --  when analysing generic actual parameters.

                  pragma Assert (No (Corresponding_Generic_Association (N)));

                  --  Check that an indexing expression of an indexed component
                  --  or the discrete range of a slice in an object renaming
                  --  declaration which renames part of that index or slice
                  --  is without variable inputs.

                  Check_Name_Indexes_And_Slices (Name (N));

                  --  Check that the prefix of a dereference in an object
                  --  renaming declaration which renames part of that
                  --  dereference is without variable inputs. Contrary to
                  --  indexing expressions and slices whose side effects are
                  --  correctly hoisted in GNATprove, we can't do the same
                  --  for naming the memory pointed to by a pointer before
                  --  the pointer is reassigned.

                  Check_Name_Dereferences (Name (N));
               end if;

            --  Check that the constrained array definition of an object
            --  declaration does not contain variable inputs.

            when N_Object_Declaration =>
               if Comes_From_Source (N) then
                  Check_Subtype_Indication (Object_Definition (N));

                  --  Check SPARK RM 4.4(2) rule about:
                  --  * the root name of the expression of an object
                  --    declaration defining a borrowing operation, except for
                  --    a single occurrence of the root object of the
                  --    expression.

                  declare
                     Indexes : Node_Lists.List;
                     --  List of indexes to check for variable input

                     procedure Collect_Indexes (Expr : Node_Id);
                     --  Append to Indexes all the indexes of indexed_component
                     --  and slice in the path expression Expr.

                     ---------------------
                     -- Collect_Indexes --
                     ---------------------

                     procedure Collect_Indexes (Expr : Node_Id) is
                     begin
                        case Nkind (Expr) is
                           when N_Expanded_Name | N_Identifier =>
                              null;

                           when N_Explicit_Dereference | N_Selected_Component
                           =>
                              Collect_Indexes (Prefix (Expr));

                           when N_Attribute_Reference =>
                              pragma
                                Assert (Attribute_Name (Expr) = Name_Access);
                              Collect_Indexes (Prefix (Expr));

                           when N_Indexed_Component =>
                              declare
                                 Ind_Expr : Node_Id :=
                                   First (Expressions (Expr));
                              begin
                                 loop
                                    Indexes.Append (Ind_Expr);
                                    Next (Ind_Expr);
                                    exit when No (Ind_Expr);
                                 end loop;
                              end;
                              Collect_Indexes (Prefix (Expr));

                           when N_Slice =>
                              Indexes.Append (Discrete_Range (Expr));
                              Collect_Indexes (Prefix (Expr));

                           when N_Qualified_Expression
                              | N_Type_Conversion
                              | N_Unchecked_Type_Conversion
                           =>
                              Collect_Indexes (Expression (Expr));

                           when others =>
                              raise Program_Error;
                        end case;
                     end Collect_Indexes;

                     Target : constant Node_Id := Defining_Entity (N);
                     Typ    : constant Entity_Id := Etype (Target);
                     Root   : Node_Id;

                  begin
                     if Is_Anonymous_Access_Object_Type (Typ)
                       and then not Is_Access_Constant (Typ)
                       and then not Is_Constant_Borrower (Target)
                     then
                        Root := Get_Observed_Or_Borrowed_Expr (Expression (N));
                        Collect_Indexes (Root);

                        for Ind_Expr of Indexes loop
                           Detect_Variable_Inputs
                             (N        => Ind_Expr,
                              Err_Desc => "borrowed expression");
                        end loop;
                     end if;
                  end;
               end if;

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

            Handler := First_Non_Pragma (Exception_Handlers (N));
            while Present (Handler) loop
               Traverse_Declarations_Or_Statements (Statements (Handler));
               Next_Non_Pragma (Handler);
            end loop;
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
               Subp_Body : constant Node_Id := Get_Body (FA.Spec_Entity);

            begin
               Traverse_Declarations_And_HSS (Subp_Body);

               --  A user-defined primitive equality operation on a record type
               --  shall have a Global aspect of NULL, unless the record type
               --  has only limited views (SPARK RM 6.1.4(11)).

               if Is_User_Defined_Equality (FA.Spec_Entity)
                 and then Is_Primitive (FA.Spec_Entity)
               then
                  declare
                     Typ     : constant Entity_Id :=
                       Etype (First_Formal (FA.Spec_Entity));
                     Globals : Global_Flow_Ids;
                  begin
                     if Is_Record_Type (Unchecked_Full_Type (Typ))
                       and then not Is_Limited_Type (Retysp (Typ))
                     then
                        Get_Globals
                          (Subprogram => FA.Spec_Entity,
                           Scope      => FA.S_Scope,
                           Classwide  => False,
                           Globals    => Globals);

                        if not (Globals.Proof_Ins.Is_Empty
                                and then Globals.Inputs.Is_Empty)
                        then
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      =>
                                "user-defined equality shall "
                                & "have a Global aspect of null",
                              SRM_Ref  => "6.6(1)",
                              N        => FA.Spec_Entity,
                              Severity => Error_Kind);
                        end if;
                     end if;
                  end;
               end if;

               --  If the node is an instance of a generic then we need to
               --  check its actuals.

               if Is_Generic_Instance (FA.Spec_Entity) then

                  --  For subprogram instances we need to get to the
                  --  wrapper package.

                  Check_Actuals (Unique_Defining_Entity (Parent (Subp_Body)));
               end if;
            end;

         when Kind_Task =>

            --  Traverse declarations and statements in the task body. We deal
            --  with the visible and private parts of the task when analysing
            --  the enclosing subprogram/package.

            Traverse_Declarations_And_HSS (Task_Body (FA.Spec_Entity));

         when Kind_Package =>
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
         pragma Annotate (Xcov, Exempt_On, "Debugging code");
         if Gnat2Why_Args.Debug_Mode then
            Error_Msg_Flow
              (FA       => FA,
               Msg      =>
                 "flow analysis of & abandoned due to"
                 & " expressions with variable inputs",
               N        => FA.Spec_Entity,
               Severity => Error_Kind,
               F1       => Direct_Mapping_Id (FA.Spec_Entity));
         end if;
         pragma Annotate (Xcov, Exempt_Off);
      end if;
   end Check_Expressions;

   --------------------------------------------------
   -- Check_Illegal_Writes_And_All_Variables_Known --
   --------------------------------------------------

   procedure Check_Illegal_Writes_And_All_Variables_Known
     (FA : in out Flow_Analysis_Graphs; Sane : out Boolean)
   is
      function In_Abstract_Contract
        (FA : Flow_Analysis_Graphs; G : Flow_Id) return Boolean
      with
        Pre =>
          FA.Kind in Kind_Subprogram | Kind_Task
          and then (Present (FA.Refined_Global_N)
                    or else Present (FA.Refined_Depends_N));
      --  Returns True if G can be found in the Global or Depends contract

      --------------------------
      -- In_Abstract_Contract --
      --------------------------

      function In_Abstract_Contract
        (FA : Flow_Analysis_Graphs; G : Flow_Id) return Boolean is
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
                     then Parse_Global_Contract (FA.Spec_Entity, FA.Global_N)
                     else
                       Parse_Depends_Contract (FA.Spec_Entity, FA.Depends_N));

                  use type Node_Sets.Set;

                  All_Globals : constant Node_Sets.Set :=
                    Raw_Globals.Inputs
                    or Raw_Globals.Outputs
                    or Raw_Globals.Proof_Ins;

               begin
                  return
                    Present (Find_In (All_Globals, Get_Direct_Mapping_Id (G)));
               end;

            when others =>
               raise Program_Error;
         end case;
      end In_Abstract_Contract;

      Aspect_To_Fix : constant String :=
        (case FA.Kind is
           when Kind_Subprogram | Kind_Task =>
             (if Present (FA.Refined_Global_N)
              then "Refined_Global"
              elsif Present (FA.Refined_Depends_N)
              then "Refined_Depends"
              elsif Present (FA.Global_N)
              then "Global"
              elsif Present (FA.Depends_N)
              then "Depends"
              else "Global"),

           when Kind_Package => "Initializes");
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

           when Kind_Package => "");
      --  A string representation of the next aspect that needs to be
      --  corrected, i.e. this is the Global/Depends aspect if a global has
      --  been detected to be missing from a Refined_Global/Refined_Depends
      --  contract but it is not mentioned in the corresponding Global/Depends.
      --  It is both Global and Depends if the global has been detected as
      --  missing either in the Refined_Global or Refined_Depends and the
      --  subprogram is annotated with both Global and Depends contracts.

      Msg : constant String :=
        (case FA.Kind is
           when Kind_Subprogram | Kind_Task =>
             "must be listed in the " & Aspect_To_Fix & " aspect of",
           when Kind_Package =>
             "must be mentioned as an input of the "
             & Aspect_To_Fix
             & " aspect of");

      SRM_Ref : constant String :=
        (case FA.Kind is
           when Kind_Subprogram | Kind_Task => "6.1.4(15)",
           when Kind_Package => "7.1.5(11)");
      --  String representation of the violated SPARK RM rule

      Unknown_Globals_In_Package : Flow_Id_Sets.Set;
      --  Unknown global variables written in the elaboration of the analysed
      --  unit if it is a package.

      --  Start of processing for Check_Illegal_Writes_And_All_Variables_Known

   begin
      Sane := True;

      --  We look for illegal updates

      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         if FA.PDG.Get_Key (V).Variant in Initial_Value | Final_Value then
            goto NEXT_VERTEX;
         end if;

         for Var of FA.Atr (V).Variables_Defined loop

            --  If we know about that particular global, then we need to
            --  check if the update is OK.

            if FA.All_Vars.Contains (Var) then

               declare
                  Corresp_Final_Vertex : constant Flow_Graphs.Vertex_Id :=
                    FA.PDG.Get_Vertex (Change_Variant (Var, Final_Value));
                  pragma
                    Assert (Corresp_Final_Vertex /= Flow_Graphs.Null_Vertex);
                  Var_Atr              : V_Attributes renames
                    FA.Atr (Corresp_Final_Vertex);
               begin
                  if Var_Atr.Is_Global and then Var_Atr.Is_Constant then
                     if FA.Kind = Kind_Package then
                        Error_Msg_Flow
                          (FA           => FA,
                           Msg          =>
                             "cannot write & during" & " elaboration of &",
                           Explain_Code => EC_Write_In_Elaboration,
                           N            => Error_Location (FA.PDG, FA.Atr, V),
                           Severity     => High_Check_Kind,
                           Tag          => Illegal_Update,
                           F1           => Var,
                           F2           => Direct_Mapping_Id (FA.Spec_Entity),
                           Vertex       => V);

                     else
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "& must be a global output of &",
                           SRM_Ref  => "6.1.4(18)",
                           N        => Error_Location (FA.PDG, FA.Atr, V),
                           Severity => High_Check_Kind,
                           F1       => Var,
                           F2       => Direct_Mapping_Id (FA.Spec_Entity),
                           Tag      => Illegal_Update,
                           Vertex   => V);
                     end if;

                     Sane := False;
                  end if;
               end;

            --  If we have a write to a variable a package knows nothing
            --  about, then it is an illegal update.

            elsif FA.Kind = Kind_Package then

               Error_Msg_Flow
                 (FA           => FA,
                  Msg          => "cannot write & during elaboration of &",
                  Explain_Code => EC_Write_In_Elaboration,
                  N            => Error_Location (FA.PDG, FA.Atr, V),
                  Severity     => High_Check_Kind,
                  Tag          => Illegal_Update,
                  F1           => Entire_Variable (Var),
                  F2           => Direct_Mapping_Id (FA.Spec_Entity),
                  Vertex       => V);

               Unknown_Globals_In_Package.Include (Entire_Variable (Var));

               Sane := False;
            end if;
         end loop;

         <<NEXT_VERTEX>>
      end loop;

      --  We look for unknown Flow_Ids

      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : V_Attributes renames FA.Atr (V);

            Variables_Referenced : constant Flow_Id_Sets.Set :=
              A.Variables_Used or A.Variables_Defined;
         begin
            for Var of Variables_Referenced loop

               --  If we are dealing with a global written in the elaboration
               --  of a package, we don't suggest to mention it as an input in
               --  the Initializes aspect of the package.

               if not Unknown_Globals_In_Package.Contains
                        (Entire_Variable (Var))
                 and then not FA.All_Vars.Contains (Var)
               then
                  declare
                     First_Var_Use : constant Node_Id :=
                       First_Variable_Use
                         (FA      => FA,
                          Var     => Var,
                          Kind    => Use_Any,
                          Precise => False);

                     Subprogram : constant Flow_Id :=
                       Direct_Mapping_Id (FA.Spec_Entity);

                     Conts : Message_Lists.List;

                  begin

                     --  If the global is missing both from the refined
                     --  contract and the abstract contract, issue a
                     --  continuation message explaining that the global
                     --  needs to be listed in the abstract contract as well.

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
                           Conts.Append
                             (Create
                                (Substitute_Message
                                   ("as a result & must be listed in the "
                                    & Next_Aspect_To_Fix
                                    & " of &",
                                    N  => First_Var_Use,
                                    F1 => Missing,
                                    F2 => Subprogram)));
                        end;
                     end if;

                     Error_Msg_Flow
                       (FA            => FA,
                        Msg           => "& " & Msg & " &",
                        SRM_Ref       => SRM_Ref,
                        N             => First_Var_Use,
                        F1            =>
                          (if Gnat2Why_Args.Flow_Advanced_Debug
                           then Var
                           else Entire_Variable (Var)),
                        Severity      => High_Check_Kind,
                        Tag           => Global_Missing,
                        F2            => Subprogram,
                        Vertex        => V,
                        Continuations => Conts);

                     Sane := False;

                  end;

                  --  Sanity check: if the Global contract is generated,
                  --  then all variables should be known. When fails,
                  --  print an offending source location (for the users)
                  --  and "Subprogram_Name @ Vertex_Id : Flow_Id (for the
                  --  developers).

                  if Gnat2Why_Args.Flow_Generate_Contracts
                    and then FA.Is_Generative
                  then
                     Current_Error_Node := A.Error_Location;

                     --  If the unknown variable is declared within the
                     --  analysed subprogram, then most likely something went
                     --  wrong with Get_Variables and it is best to crash;
                     --  otherwise, the problem is rather in the GG machinery
                     --  and the users are likely to workaround the problem
                     --  by adding explicit Global aspect, as suggested by
                     --  the error message.

                     if Var.Kind in Direct_Mapping | Record_Field
                       and then Scope_Within
                                  (Inner => Get_Direct_Mapping_Id (Var),
                                   Outer => FA.Spec_Entity)
                     then
                        raise Program_Error
                          with
                            Full_Source_Name (FA.Spec_Entity)
                            & " @"
                            & V'Img
                            & " : "
                            & Flow_Id_To_String (Var);
                     else
                        pragma
                          Assert
                            (False,
                             Full_Source_Name (FA.Spec_Entity)
                               & " @"
                               & V'Img
                               & " : "
                               & Flow_Id_To_String (Var));
                     end if;
                  end if;
               end if;
            end loop;
         end;
      end loop;
   end Check_Illegal_Writes_And_All_Variables_Known;

   ------------------------------------
   -- Check_Generated_Refined_Global --
   ------------------------------------

   procedure Check_Generated_Refined_Global
     (FA : in out Flow_Analysis_Graphs; Sane : out Boolean)
   is
      Error_Loc : constant Node_Id :=
        (if Ekind (FA.Spec_Entity) = E_Package
         then Empty
         else (if Present (FA.Global_N) then FA.Global_N else FA.Depends_N));
      --  Location for posting errors; it is either the Global (preferred) or
      --  the Depends contract, just like in Get_Global routine, which prefers
      --  the Global but uses the Depends as a fallback.

      procedure Check
        (Generated : Flow_Id_Sets.Set;
         User      : Flow_Id_Sets.Set;
         Missing   : out Flow_Id_Sets.Set;
         Unused    : out Flow_Id_Sets.Set)
      with
        Post =>
          Missing.Is_Subset (Of_Set => Generated)
          and then Unused.Is_Subset (Of_Set => User);
      --  Compute missing and unused user globals based on generated and those
      --  provided by the user.

      procedure Error_Msg (Msg : String; Severity : Msg_Severity; F : Flow_Id);
      --  Wrapper to simplify reporting errors about missing and unused globals

      -----------
      -- Check --
      -----------

      procedure Check
        (Generated : Flow_Id_Sets.Set;
         User      : Flow_Id_Sets.Set;
         Missing   : out Flow_Id_Sets.Set;
         Unused    : out Flow_Id_Sets.Set) is
      begin
         Missing := Flow_Id_Sets.Empty_Set;
         Unused := User;

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
         Tag : constant Flow_Tag_Kind :=
           (if Severity = Error_Kind
            then Critical_Global_Missing
            else Global_Missing);
      begin
         Sane := False;

         Error_Msg_Flow
           (FA       => FA,
            Msg      => Msg,
            N        => Error_Loc,
            Severity => Severity,
            F1       => F,
            F2       => Direct_Mapping_Id (FA.Spec_Entity),
            Tag      => Tag);
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
         Raw_Globals :=
           Parse_Global_Contract
             (Subprogram => FA.Spec_Entity, Global_Node => FA.Global_N);

      elsif Present (FA.Depends_N) then
         Raw_Globals :=
           Parse_Depends_Contract
             (Subprogram => FA.Spec_Entity, Depends_Node => FA.Depends_N);

      else
         pragma
           Assert
             (Is_Pure (FA.Spec_Entity)
                or else Is_Null_Procedure (FA.Spec_Entity));
      end if;

      --  Convert user-globals from Entity_Ids to Flow_Ids

      User_Global :=
        (Proof_Ins => To_Flow_Id_Set (Raw_Globals.Proof_Ins, In_View),
         Inputs    => To_Flow_Id_Set (Raw_Globals.Inputs, In_View),
         Outputs   => To_Flow_Id_Set (Raw_Globals.Outputs, Out_View));

      --  Read the generated Refined_Global

      Get_Globals
        (Subprogram => FA.Spec_Entity,
         Scope      => FA.B_Scope,
         Classwide  => False,
         Globals    => Generated_Refined_Global);

      --  Up project actual globals

      Up_Project (Generated_Refined_Global, Generated_Global, FA.S_Scope);

      --  Detect inconsistent globals

      Check
        (Generated => Generated_Global.Inputs,
         User      => User_Global.Inputs,
         Missing   => Missing_Inputs,
         Unused    => Unused_Inputs);

      Check
        (Generated => Generated_Global.Outputs,
         User      => User_Global.Outputs,
         Missing   => Missing_Outputs,
         Unused    => Unused_Outputs);

      Check
        (Generated => Generated_Global.Proof_Ins,
         User      => User_Global.Proof_Ins,
         Missing   => Missing_Proof_Ins,
         Unused    => Unused_Proof_Ins);

      --  Flag missing user globals

      for Missing of Missing_Inputs loop
         Error_Msg
           (Msg      =>
              "& must be a global "
              & (if Present
                      (Find_In
                         (User_Global.Outputs,
                          Change_Variant (Missing, Out_View)))
                 then "In_Out of &"
                 else "Input of &"),
            Severity => Medium_Check_Kind,
            F        => Missing);
      end loop;

      for Missing of Missing_Outputs loop
         Error_Msg
           (Msg      =>
              "& must be a global "
              & (if Present
                      (Find_In
                         (User_Global.Inputs,
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
     (FA : in out Flow_Analysis_Graphs; Sane : out Boolean) is
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
                           Msg      =>
                             "protected function with effective "
                             & "reads & is not allowed in SPARK",
                           N        =>
                             (if Present (Atr.Error_Location)
                              then Atr.Error_Location
                              else FA.Spec_Entity),
                           F1       => Var,
                           Severity => Error_Kind,
                           Tag      => Side_Effects,
                           Vertex   => V);
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
