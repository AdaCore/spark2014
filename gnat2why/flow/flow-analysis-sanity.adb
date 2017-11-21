------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . A N A L Y S I S . S A N I T Y                  --
--                                                                          --
--                                B o d y                                   --
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

--  This package implements a variety of sanity checks that are run before
--  the rest of flow analysis is performed.

with Sem_Aux;                use Sem_Aux;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;

with Checked_Types;          use Checked_Types;
with Gnat2Why_Args;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with SPARK_Util.Types;       use SPARK_Util.Types;
with SPARK_Util;             use SPARK_Util;
with VC_Kinds;               use VC_Kinds;

with Flow_Error_Messages;    use Flow_Error_Messages;
with Flow_Utility;           use Flow_Utility;
with Flow_Refinement;        use Flow_Refinement;

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
   begin
      Sane := True;

      if Ekind (FA.Analyzed_Entity) = E_Function
        and then FA.Function_Side_Effects_Present
      then
         if Gnat2Why_Args.Debug_Mode then
            Error_Msg_Flow
              (FA       => FA,
               Msg      => "flow analysis of & abandoned due to " &
                           "function with side effects",
               N        => FA.Analyzed_Entity,
               Severity => Error_Kind,
               F1       => Direct_Mapping_Id (FA.Analyzed_Entity));
         end if;

         Sane := False;
      end if;
   end Check_Function_Side_Effects;

   -----------------------
   -- Check_Expressions --
   -----------------------

   procedure Check_Expressions
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean)
   is
      Entry_Node : Node_Id;

      function Check_Expression (N : Node_Id) return Traverse_Result;
      --  Helper function to walk over the tree

      procedure Check_Variable_Inputs
        (Flow_Ids : Ordered_Flow_Id_Sets.Set;
         Err_Desc : String;
         Err_Node : Node_Id);
      --  Issues an error for any member of the Flow_Ids which does NOT denote
      --  a constant, a bound or a discriminant (of an enclosing concurrent
      --  type).

      procedure Handle_Parameters (Formal : Node_Id; Actual : Node_Id);
      --  Checks that for a generic instance there is no Actual with variable
      --  inputs corresponding to a Formal object declaration with mode in.

      function Variables (N : Node_Id) return Ordered_Flow_Id_Sets.Set
      is
        (To_Ordered_Flow_Id_Set
           (Get_Variables (N,
                           Scope                        => FA.B_Scope,
                           Local_Constants              => Node_Sets.Empty_Set,
                           Fold_Functions               => False,
                           Use_Computed_Globals         => True,
                           Expand_Synthesized_Constants => True)));
      --  A helpful wrapper around Get_Variables as it is used in this sanity
      --  checking procedure.

      function Variables (L : List_Id) return Ordered_Flow_Id_Sets.Set
      is
        (To_Ordered_Flow_Id_Set
           (Get_Variables (L,
                           Scope                        => FA.B_Scope,
                           Local_Constants              => Node_Sets.Empty_Set,
                           Fold_Functions               => False,
                           Use_Computed_Globals         => True,
                           Expand_Synthesized_Constants => True)));
      --  As above

      ----------------------
      -- Check_Expression --
      ----------------------

      function Check_Expression (N : Node_Id) return Traverse_Result is

         function Check_Renaming (N : Node_Id) return Traverse_Result;
         --  Checks that indexed components and slices in object renaming
         --  declarations do not have variable inputs.

         --------------------
         -- Check_Renaming --
         --------------------

         function Check_Renaming (N : Node_Id) return Traverse_Result is
         begin
            case Nkind (N) is
               when N_Indexed_Component =>
                  Check_Variable_Inputs
                    (Flow_Ids => Variables (Expressions (N)),
                     Err_Desc => "renamed index",
                     Err_Node => N);

               when N_Slice =>
                  Check_Variable_Inputs
                    (Flow_Ids => Variables (Discrete_Range (N)),
                     Err_Desc => "renamed slice",
                     Err_Node => Discrete_Range (N));

               when others =>
                  null;
            end case;

            return OK; -- Keep searching in case of nested prefixes
         end Check_Renaming;

         procedure Check_Name_Indexes_And_Slices is new
           Traverse_Proc (Check_Renaming);

      --  Start of processing for Check_Expression

      begin
         case Nkind (N) is
            when N_Subprogram_Body
               | N_Package_Specification
               | N_Package_Body
            =>

               --  We do not want to process declarations of any nested
               --  subprograms or packages. These will be analyzed by their
               --  own pass of flow analysis.

               if N = Entry_Node then
                  return OK;
               else
                  return Skip;
               end if;

            when N_Full_Type_Declaration
               | N_Subtype_Declaration
               | N_Private_Type_Declaration
               | N_Private_Extension_Declaration
            =>
               declare
                  Typ : constant Type_Id := Defining_Identifier (N);

               begin
                  if Has_Predicates (Typ) then
                     declare
                        Predicate_Func : constant Entity_Id :=
                          Predicate_Function (Typ);

                     begin
                        if Present (Predicate_Func) then
                           Check_Variable_Inputs
                             (Flow_Ids =>
                                Variables
                                  (Get_Expr_From_Return_Only_Func
                                       (Predicate_Func)),
                              Err_Desc => "predicate",
                              Err_Node => Typ);
                        end if;
                     end;
                  end if;

                  --  Has_Invariants_In_SPARK operates on the public view of a
                  --  type and therefore we use call it on private type
                  --  delcarations or extensions.
                  if Nkind (N) in N_Private_Type_Declaration
                                | N_Private_Extension_Declaration
                    and then Has_Invariants_In_SPARK (Typ)
                  then
                     --  This is the check for 7.3.2(3) [which is really
                     --  4.4(2)] and the check for 7.3.2(4).
                     declare
                        Expr : constant Node_Id :=
                          Get_Expr_From_Check_Only_Proc
                            (Invariant_Procedure (Typ));

                        Funs : constant Node_Sets.Set :=
                          Get_Functions (Expr, Include_Predicates => False);

                     begin
                        --  Check 4.4(2) (no variable inputs)
                        Check_Variable_Inputs
                          (Flow_Ids => Variables (Expr),
                           Err_Desc => "invariant",
                           Err_Node => Full_View (Typ));

                        --  Check 7.3.2(4) (no calls to boundary subprograms)
                        for F of Funs loop
                           if Is_Boundary_Subprogram_For_Type (F, Typ) then
                              Error_Msg_Flow
                                (FA       => FA,
                                 Msg      =>
                                   "cannot call boundary subprogram & " &
                                   "for type & in its own invariant",
                                 Severity => High_Check_Kind,
                                 N        => Full_View (Typ),
                                 F1       => Direct_Mapping_Id (F),
                                 F2       => Direct_Mapping_Id (Typ),
                                 SRM_Ref  => "7.3.2(4)");
                           end if;
                        end loop;
                     end;
                  end if;
               end;
               return OK;

            when N_Loop_Parameter_Specification =>

               --  In a loop parameter specification, variables are allowed
               --  in the range constraint, so the tree walk is pruned here.

               return Skip;

            when N_Object_Renaming_Declaration =>
               if Comes_From_Source (N) then
                  Check_Name_Indexes_And_Slices (Name (N));
               end if;
               return Skip;

            when N_Subtype_Indication =>
               --  We do not sanity check subtype declaration generated by the
               --  front end; see N116-011 and NA18-003.

               declare
                  Parent_N : constant Node_Id := Parent (N);
               begin
                  if Nkind (Parent_N) = N_Subtype_Declaration
                    and then Is_Internal (Defining_Identifier (Parent_N))
                  then
                     return Skip;
                  end if;
               end;

               declare
                  C : constant Node_Id := Constraint (N);
               begin
                  case Nkind (C) is
                     when N_Range_Constraint =>
                        --  Note that fetching the Variables for C returns the
                        --  union of the sets of the low-bound and the
                        --  high-bound.
                        Check_Variable_Inputs
                          (Flow_Ids => Variables (C),
                           Err_Desc => "subtype constraint",
                           Err_Node => C);
                        return Skip;

                     when N_Index_Or_Discriminant_Constraint =>
                        Check_Variable_Inputs
                          (Flow_Ids => Variables (Constraints (C)),
                           Err_Desc => "subtype constraint",
                           Err_Node => C);
                        return Skip;

                     when N_Delta_Constraint
                        | N_Digits_Constraint
                     =>

                        --  Ada LRM requires these constraints to be
                        --  static, so no further action required here.

                        return Skip;

                     when others =>
                        raise Program_Error;
                  end case;
               end;

            when N_Component_Declaration
               | N_Discriminant_Specification
            =>
               declare
                  Default_Expression : constant Node_Id := Expression (N);
               begin
                  if Present (Default_Expression) then
                     Check_Variable_Inputs
                       (Flow_Ids => Variables (Default_Expression),
                        Err_Desc => "default initialization",
                        Err_Node => Default_Expression);
                  end if;
               end;
               return Skip;

            when others =>
               return OK;
         end case;
      end Check_Expression;

      ---------------------------
      -- Check_Variable_Inputs --
      ---------------------------

      procedure Check_Variable_Inputs
        (Flow_Ids : Ordered_Flow_Id_Sets.Set;
         Err_Desc : String;
         Err_Node : Node_Id)
      is
      begin
         for F of Flow_Ids loop
            if (F.Kind in Direct_Mapping | Record_Field
                and then Nkind (Get_Direct_Mapping_Id (F)) in N_Entity
                and then not (Is_Constant_Object (Get_Direct_Mapping_Id (F))
                              or else Is_Bound (F)
                              or else Ekind (Get_Direct_Mapping_Id (F)) =
                                E_Discriminant))
              or else
                F.Kind = Magic_String
            then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => Err_Desc &
                              " cannot depend on variable input &",
                  SRM_Ref  => "4.4(2)",
                  N        => Err_Node,
                  Severity => Error_Kind,
                  F1       => Entire_Variable (F));
               Sane := False;
            end if;
         end loop;
      end Check_Variable_Inputs;

      -----------------------
      -- Handle_Parameters --
      -----------------------

      procedure Handle_Parameters (Formal : Node_Id;
                                   Actual : Node_Id)
      is
      begin
         if Nkind (Formal) = N_Formal_Object_Declaration then
            declare
               Formal_E : constant Entity_Id := Defining_Entity (Formal);

            begin
               if Ekind (Formal_E) = E_Generic_In_Parameter then
                  Check_Variable_Inputs
                    (Flow_Ids => Variables (Actual),
                     Err_Desc => "actual for formal object with mode in",
                     Err_Node => Actual);
               end if;
            end;
         end if;
      end Handle_Parameters;

      procedure Check_Actuals is new
        Iterate_Generic_Parameters (Handle_Parameters);

      procedure Do_Checks is new Traverse_Proc (Check_Expression);

   --  Start of processing for Check_Expressions

   begin
      Sane := True;

      --  Please don't try to simplify/delete Entry_Node here, it is also a
      --  global in Do_Checks.

      case FA.Kind is
         when Kind_Subprogram =>
            Entry_Node := Get_Body (FA.Analyzed_Entity);
            Do_Checks (Entry_Node);

            if Is_User_Defined_Equality (FA.Spec_Entity) then
               declare
                  Typ : constant Entity_Id :=
                    Get_Full_Type_Without_Checking
                      (First_Formal (FA.Spec_Entity));

               begin
                  if Ekind (Typ) in Record_Kind then
                     Check_Variable_Inputs
                       (Flow_Ids => Variables
                          (Get_Expr_From_Return_Only_Func (FA.Spec_Entity)),
                        Err_Desc => "user-defined equality",
                        Err_Node => FA.Spec_Entity);
                  end if;
               end;
            end if;

            --  If the node is an instance of a generic then we need to check
            --  its actuals.
            if Is_Generic_Instance (FA.Analyzed_Entity) then
               --  For subprogram instances we need to get to the
               --  wrapper package.
               Check_Actuals (Unique_Defining_Entity (Parent (Entry_Node)));
            end if;

         when Kind_Task =>
            Entry_Node := Task_Body (FA.Analyzed_Entity);
            Do_Checks (Entry_Node);

         when Kind_Package =>
            Entry_Node := Package_Specification (FA.Analyzed_Entity);
            Do_Checks (Entry_Node);

            --  If the node is an instance of a generic then we need to check
            --  its actuals.
            if Is_Generic_Instance (FA.Spec_Entity) then
               Check_Actuals (FA.Spec_Entity);
            end if;

         when Kind_Package_Body =>
            Entry_Node := Package_Specification (FA.Spec_Entity);
            Do_Checks (Entry_Node);

            --  If the node is an instance of a generic then we need to check
            --  its actuals.
            if Is_Generic_Instance (FA.Spec_Entity) then
               Check_Actuals (FA.Spec_Entity);
            end if;

            Entry_Node := Package_Body (FA.Analyzed_Entity);
            Do_Checks (Entry_Node);
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

            Written_Vars : constant Ordered_Flow_Id_Sets.Set :=
              To_Ordered_Flow_Id_Set (A.Variables_Defined);

            F                    : Flow_Id;
            Corresp_Final_Vertex : Flow_Graphs.Vertex_Id;
            Final_Atr            : V_Attributes;
         begin
            for Var of Written_Vars loop
               F := Change_Variant (Var, Normal_Use);

               if FA.Kind in Kind_Package | Kind_Package_Body and then
                 not (FA.All_Vars.Contains (F) or else Synthetic (F))
               then

                  --  We have a write to a variable a package knows
                  --  nothing about. This is always an illegal update.

                  case F.Kind is
                     when Direct_Mapping
                        | Record_Field
                        | Magic_String
                     =>
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "cannot write & during" &
                                       " elaboration of &",
                           SRM_Ref  => "7.7.1(6)",
                           N        => Error_Location (FA.PDG, FA.Atr, V),
                           Severity => High_Check_Kind,
                           F1       => Entire_Variable (Var),
                           F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Vertex   => V);

                     when others =>
                        raise Program_Error;
                  end case;
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
                    and then not Final_Atr.Is_Loop_Parameter
                  then
                     if FA.Kind in Kind_Package | Kind_Package_Body then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "cannot write & during" &
                                       " elaboration of &",
                           SRM_Ref  => "7.7.1(6)",
                           N        => Error_Location (FA.PDG, FA.Atr, V),
                           Severity => High_Check_Kind,
                           F1       => Var,
                           F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Vertex   => V);

                     else
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "& must be a global output of &",
                           SRM_Ref  => "6.1.4(16)",
                           N        => Error_Location (FA.PDG, FA.Atr, V),
                           Severity => High_Check_Kind,
                           F1       => (if A.Is_Parameter
                                        then A.Parameter_Formal
                                        else Var),
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
              (if Present (FA.Refined_Global_N)
               then "Refined_Global"
               elsif Present (FA.Global_N)
               then (if Present (FA.Refined_Depends_N)
                     then "Refined_Depends"
                     else "Global")
               elsif Present (FA.Depends_N)
               then (if Present (FA.Refined_Depends_N)
                     then "Refined_Depends"
                     else "Depends")
               else "Global"),
            when Kind_Package | Kind_Package_Body  =>
               "Initializes");
      --  A string representation of the aspect that needs to be corrected

      SRM_Ref : constant String :=
        (case FA.Kind is
            when Kind_Subprogram | Kind_Task      => "6.1.4(13)",
            when Kind_Package | Kind_Package_Body => "7.1.5(12)");
      --  String representation of the violated SPARK RM rule

   begin
      Sane := True;

      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : V_Attributes renames FA.Atr (V);

            Variables_Referenced : constant Ordered_Flow_Id_Sets.Set :=
              To_Ordered_Flow_Id_Set (A.Variables_Used or A.Variables_Defined);

         begin
            for Var of Variables_Referenced loop

               --  Ignore known variables and synthetic null export
               if FA.All_Vars.Contains (Change_Variant (Var, Normal_Use))
                    or else
                  Synthetic (Var)
               then
                  null;

               --  Here we are dealing with a missing global

               else
                  case Var.Kind is
                     when Direct_Mapping
                        | Record_Field
                        | Magic_String
                     =>
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "& must be listed in the " &
                                       Aspect_To_Fix & " aspect of &",
                           SRM_Ref  => SRM_Ref,
                           N        => First_Variable_Use (FA      => FA,
                                                           Var     => Var,
                                                           Kind    => Use_Any,
                                                           Precise => False),
                           F1       => (if Gnat2Why_Args.Flow_Advanced_Debug
                                        then Var
                                        else Entire_Variable (Var)),
                           Severity => High_Check_Kind,
                           F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Vertex   => V);

                     when others =>
                        raise Program_Error;
                  end case;

                  Sane := False;
               end if;
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

      function Find_In (User : Flow_Id_Sets.Set; G : Flow_Id) return Flow_Id
      with Post => (if Present (Find_In'Result)
                    then User.Contains (Find_In'Result));
      --  If a generated global G is represented by User ones, either directly
      --  or via an abstract state, then return the representative user global;
      --  otherwise, return Null_Flow_Id.

      function Is_Dummy_Abstract_State (F : Flow_Id) return Boolean;
      --  Returns True if F is an abstract state that can be determined
      --  to have no constituents. Such abstract states are most likely
      --  just placeholders and will be later removed or populated with
      --  constituents.

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

         for A of Generated loop
            declare
               U : constant Flow_Id := Find_In (User, A);

            begin
               if Present (U) then
                  Unused.Exclude (U);
               else
                  Missing.Insert (A);
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

      -------------
      -- Find_In --
      -------------

      function Find_In (User : Flow_Id_Sets.Set; G : Flow_Id) return Flow_Id is
      begin
         if User.Contains (G) then
            return G;
         elsif Is_Constituent (G) then
            return Find_In (User, Encapsulating_State (G));
         else
            return Null_Flow_Id;
         end if;
      end Find_In;

      -----------------------------
      -- Is_Dummy_Abstract_State --
      -----------------------------

      function Is_Dummy_Abstract_State (F : Flow_Id) return Boolean is
      begin
         if F.Kind = Direct_Mapping then
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);
            begin
               return Ekind (E) = E_Abstract_State
                 and then (Is_Null_State (E)
                           or else
                             (State_Refinement_Is_Visible (E, FA.B_Scope)
                              and then Has_Null_Refinement (E)));
            end;
         else
            return False;
         end if;
      end Is_Dummy_Abstract_State;

      --  Local variables:

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

      --  Read the user Global/Depends contract; Use_Deduced_Globals is False
      --  to prevent trimming based on generated (refined) globals.
      Get_Globals (Subprogram          => FA.Analyzed_Entity,
                   Scope               => FA.S_Scope,
                   Classwide           => False,
                   Globals             => User_Global,
                   Use_Deduced_Globals => False);

      --  Read the generated Global
      Get_Globals (Subprogram => FA.Analyzed_Entity,
                   Scope      => FA.B_Scope,
                   Classwide  => False,
                   Globals    => Generated_Refined_Global);

      --  Up project actual globals
      Up_Project (Generated_Refined_Global, Generated_Global, FA.S_Scope);

      --  Detect insonsistent globals

      Check (Generated => Generated_Global.Reads,
             User      => User_Global.Reads,
             Missing   => Missing_Inputs,
             Unused    => Unused_Inputs);

      Check (Generated => Generated_Global.Writes,
             User      => User_Global.Writes,
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
                           (Find_In (User_Global.Writes,
                                     Change_Variant (Missing, Out_View)))
                         then "In_Out of &"
                         else "input of &"),
            Severity => Medium_Check_Kind,
            F        => Missing);
      end loop;

      for Missing of Missing_Outputs loop
         Error_Msg
           (Msg      => "& must be a global " &
                        (if Present
                           (Find_In (User_Global.Reads,
                                     Change_Variant (Missing, In_View)))
                         then "In_Out of &"
                         else "output of &"),
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
         if not Is_Dummy_Abstract_State (Unused) then
            Error_Msg
              (Msg      => "global input & of & not read",
               Severity => Low_Check_Kind,
               F        => Unused);
         end if;
      end loop;

      for Unused of Unused_Outputs loop
         if not Is_Dummy_Abstract_State (Unused) then
            Error_Msg
              (Msg      => "global output & of & not written",
               Severity => Error_Kind,
               F        => Unused);
         end if;
      end loop;

      for Unused of Unused_Proof_Ins loop
         if not Is_Dummy_Abstract_State (Unused) then
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
         for F of FA.All_Vars loop
            if Belongs_To_Protected_Type (F)
              and then Has_Effective_Reads (F)
            then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "protected function with effective reads & is " &
                              "not allowed in SPARK",
                  N        => FA.Spec_Entity,
                  F1       => F,
                  Severity => Error_Kind,
                  Tag      => Side_Effects);

               Sane := False;
            end if;
         end loop;
      end if;
   end Check_Side_Effects_In_Protected_Functions;

end Flow.Analysis.Sanity;
