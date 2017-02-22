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

with Nlists;                 use Nlists;
with Sem_Aux;                use Sem_Aux;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Snames;                 use Snames;

with Checked_Types;          use Checked_Types;
with Common_Iterators;       use Common_Iterators;
with Gnat2Why_Args;
with SPARK_Definition;       use SPARK_Definition;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with SPARK_Util.Types;       use SPARK_Util.Types;
with SPARK_Util;             use SPARK_Util;
with VC_Kinds;               use VC_Kinds;

with Flow_Error_Messages;    use Flow_Error_Messages;
with Flow_Utility;           use Flow_Utility;

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

      function Simple_Variable_Set (N : Node_Id)
                                    return Ordered_Flow_Id_Sets.Set
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

      function Simple_Variable_Set (L : List_Id)
                                    return Ordered_Flow_Id_Sets.Set
      is
        (To_Ordered_Flow_Id_Set
           (Get_Variables (L,
                           Scope                        => FA.B_Scope,
                           Local_Constants              => Node_Sets.Empty_Set,
                           Fold_Functions               => False,
                           Use_Computed_Globals         => True,
                           Expand_Synthesized_Constants => True)));
      --  As above.

      ----------------------
      -- Check_Expression --
      ----------------------

      function Check_Expression (N : Node_Id) return Traverse_Result
      is
         procedure Check_Flow_Id_Set
           (Flow_Ids : Ordered_Flow_Id_Sets.Set;
            Err_Desc : String;
            Err_Node : Node_Id);
         --  Issues an error for any member of the Flow_Ids which does NOT
         --  denote a constant, a bound or a discriminant (of an enclosing
         --  concurrent type).

         function Check_Name (N : Node_Id) return Traverse_Result;
         --  Checks indexed components and slices which are part of a Name
         --  subtree.

         -----------------------
         -- Check_Flow_Id_Set --
         -----------------------

         procedure Check_Flow_Id_Set
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
                     Msg      => Err_Desc & " cannot depend on &",
                     SRM_Ref  => "4.4(2)",
                     N        => Err_Node,
                     Severity => Error_Kind,
                     F1       => F);
                  Sane := False;
               end if;
            end loop;
         end Check_Flow_Id_Set;

         ----------------
         -- Check_Name --
         ----------------

         function Check_Name (N : Node_Id) return Traverse_Result is
         begin
            case Nkind (N) is
               when N_Indexed_Component =>
                  declare
                     Renamed_Indexes : constant List_Id := Expressions (N);

                     Deps : constant Ordered_Flow_Id_Sets.Set :=
                       Simple_Variable_Set (Renamed_Indexes);
                  begin
                     Check_Flow_Id_Set (Flow_Ids => Deps,
                                        Err_Desc => "renamed index",
                                        Err_Node => N);
                  end;

               when N_Slice =>
                  declare
                     Renamed_Slice : constant Node_Id := Discrete_Range (N);

                     Deps : constant Ordered_Flow_Id_Sets.Set :=
                       Simple_Variable_Set (Renamed_Slice);
                  begin
                     Check_Flow_Id_Set (Flow_Ids => Deps,
                                        Err_Desc => "renamed slice",
                                        Err_Node => Renamed_Slice);
                  end;

               when others =>
                  null;
            end case;

            return OK; -- Keep searching in case of nested prefixes
         end Check_Name;

         procedure Check_Name_Indexes_And_Slices is new
           Traverse_Proc (Check_Name);

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
               | N_Private_Extension_Declaration
            =>
               declare
                  Typ : constant Type_Id := Defining_Identifier (N);
               begin
                  if Has_Predicates (Typ) then
                     declare
                        GP, GI, GO : Flow_Id_Sets.Set;
                        Deps       : Ordered_Flow_Id_Sets.Set;
                     begin
                        Get_Globals (Subprogram => Predicate_Function (Typ),
                                     Scope      => FA.B_Scope,
                                     Classwide  => False,
                                     Proof_Ins  => GP,
                                     Reads      => GI,
                                     Writes     => GO);
                        pragma Assert (GO.Is_Empty);

                        for F of GP loop
                           Deps.Insert (Change_Variant (F, Normal_Use));
                        end loop;
                        for F of GI loop
                           Deps.Insert (Change_Variant (F, Normal_Use));
                        end loop;
                        Check_Flow_Id_Set (Flow_Ids => Deps,
                                           Err_Desc => "predicate",
                                           Err_Node => Typ);
                     end;
                  end if;

                  if Has_Invariants_In_SPARK (Typ) then
                     --  This is the check for 7.3.2(3) [which is really
                     --  4.4(2)] and the check for 7.3.2(4).
                     declare
                        IP   : constant Entity_Id := Invariant_Procedure (Typ);
                        Expr : constant Node_Id :=
                          Get_Expr_From_Check_Only_Proc (IP);
                        Vars : constant Flow_Id_Sets.Set :=
                          Get_Variables
                            (Expr,
                             Scope                => FA.B_Scope,
                             Local_Constants      => Node_Sets.Empty_Set,
                             Fold_Functions       => False,
                             Use_Computed_Globals => True,
                             Reduced              => True);
                        Funs : constant Node_Sets.Set :=
                          Get_Functions
                            (Expr,
                             Include_Predicates => False);
                     begin
                        --  Check 4.4(2) (no variable inputs)
                        Check_Flow_Id_Set (Flow_Ids => To_Ordered_Flow_Id_Set
                                             (Vars),
                                           Err_Desc => "invariant",
                                           Err_Node => Typ);

                        --  Check 7.3.2(4) (no calls to boundary subprograms)
                        for F of Funs loop
                           if Is_Boundary_Subprogram_For_Type (F, Typ) then
                              Error_Msg_Flow
                                (FA       => FA,
                                 Msg      =>
                                   "cannot call boundary subprogram & " &
                                   "for type & in its own invariant",
                                 Severity => High_Check_Kind,
                                 N        => Typ,
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
                    and then Is_Internal (Defining_Identifier (Parent (N)))
                  then
                     return Skip;
                  end if;
               end;

               declare
                  C : constant Node_Id := Constraint (N);
               begin
                  case Nkind (C) is
                     when N_Range_Constraint =>
                        declare
                           --  Note that fetching the variable set for C
                           --  returns the union of the sets of the low-bound
                           --  and the high-bound.

                           Deps : constant Ordered_Flow_Id_Sets.Set :=
                             Simple_Variable_Set (C);
                        begin
                           Check_Flow_Id_Set (Flow_Ids => Deps,
                                              Err_Desc => "subtype constraint",
                                              Err_Node => C);
                        end;

                        return Skip;

                     when N_Index_Or_Discriminant_Constraint =>
                        declare
                           Deps : constant Ordered_Flow_Id_Sets.Set :=
                             Simple_Variable_Set (Constraints (C));
                        begin
                           Check_Flow_Id_Set (Flow_Ids => Deps,
                                              Err_Desc => "subtype constraint",
                                              Err_Node => C);
                        end;

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

               if Present (Expression (N)) then
                  declare
                     Deps : constant Ordered_Flow_Id_Sets.Set :=
                       Simple_Variable_Set (Expression (N));
                  begin
                     Check_Flow_Id_Set (Flow_Ids => Deps,
                                        Err_Desc => "default initialization",
                                        Err_Node => Expression (N));
                  end;
               end if;

               return Skip;

            when others =>
               return OK;
         end case;
      end Check_Expression;

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

         when Kind_Task =>
            Entry_Node := Task_Body (FA.Analyzed_Entity);
            Do_Checks (Entry_Node);

         when Kind_Package =>
            Entry_Node := Package_Specification (FA.Analyzed_Entity);
            Do_Checks (Entry_Node);

         when Kind_Package_Body =>
            Entry_Node := Package_Specification (FA.Spec_Entity);
            Do_Checks (Entry_Node);

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
                     =>
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "cannot write & during" &
                                       " elaboration of &",
                           SRM_Ref  => "7.7.1(6)",
                           N        => Error_Location (FA.PDG, FA.Atr, V),
                           Severity => Error_Kind,
                           F1       => Entire_Variable (Var),
                           F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Vertex   => V);

                     when Magic_String =>
                        Global_Required (FA, Var);

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
                           Severity => Error_Kind,
                           F1       => Var,
                           F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Vertex   => V);

                     else
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "& must be a global output of &",
                           SRM_Ref  => "6.1.4(16)",
                           N        => Error_Location (FA.PDG, FA.Atr, V),
                           Severity => Error_Kind,
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
                           Severity => Error_Kind,
                           F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Vertex   => V);

                     when Magic_String =>
                        Global_Required (FA, Var);

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

      --  Globals provided by the user
      User_Proof_Ins             : Flow_Id_Sets.Set;
      User_Reads                 : Flow_Id_Sets.Set;
      User_Writes                : Flow_Id_Sets.Set;

      --  Globals calculated by the tools
      Actual_Proof_Ins           : Flow_Id_Sets.Set;
      Actual_Reads               : Flow_Id_Sets.Set;
      Actual_Writes              : Flow_Id_Sets.Set;

      --  Calculated globals projected upwards
      Projected_Actual_Proof_Ins : Flow_Id_Sets.Set;
      Projected_Actual_Reads     : Flow_Id_Sets.Set;
      Projected_Actual_Writes    : Flow_Id_Sets.Set;

      function Extended_Set_Contains
        (F  : Flow_Id;
         FS : Flow_Id_Sets.Set)
         return Boolean;
      --  Returns True iff F is either directly contained in FS or it is a
      --  state abstraction that encloses an element of FS.
      --  The purpose of this function is to allow user contracts to mention
      --  either a state abstraction, or the constituents thereof when both
      --  are visible.
      --  @param F is the Flow_Id that we look for
      --  @param FS is the Flow_Set in which we look
      --  @return whether FS contains F or a contituent of F

      function State_Partially_Written
        (F : Flow_Id)
        return Boolean;
      --  Returns True if F represents a state abstraction
      --  that is partially written.

      function Up_Project_Flow_Set
        (FS      : Flow_Id_Sets.Set;
         Variant : Flow_Id_Variant)
        return Flow_Id_Sets.Set;
      --  Up projects the elements of FS that can be up
      --  projected. Elements that cannot be up projected are simply
      --  copied across. The variant of all elements is also set to
      --  Variant.
      --  @param FS is the Flow_Id_Set that will be up projected
      --  @param Variant is the Flow_Id_Variant that all Flow_Ids will have
      --  @return the up projected version of FS

      ---------------------------
      -- Extended_Set_Contains --
      ---------------------------

      function Extended_Set_Contains
        (F  : Flow_Id;
         FS : Flow_Id_Sets.Set)
         return Boolean
      is
      begin
         --  Return True if F is directly contained in FS
         if FS.Contains (F) then
            return True;
         end if;

         --  Check if F is a state abstraction that encapsulates a constituent
         --  mentioned in FS.

         if Is_Abstract_State (F) then
            declare
               State : constant Entity_Id := Get_Direct_Mapping_Id (F);
            begin
               for Constit of FS loop
                  if Constit.Kind in Direct_Mapping | Record_Field then
                     declare
                        Encapsulator : constant Entity_Id :=
                          Encapsulating_State
                            (Get_Direct_Mapping_Id
                               (Constit));

                     begin
                        if Present (Encapsulator)
                          and then Encapsulator = State
                        then
                           return True;
                        end if;
                     end;
                  end if;
               end loop;
            end;
         end if;

         return False;
      end Extended_Set_Contains;

      -----------------------------
      -- State_Partially_Written --
      -----------------------------

      function State_Partially_Written
        (F : Flow_Id)
        return Boolean
      is
         E : constant Entity_Id := Get_Direct_Mapping_Id (F);
      begin
         --  Trivially False when we are not dealing with a
         --  state abstraction.
         if Ekind (E) /= E_Abstract_State then
            return False;
         end if;

         declare
            Constit             : Flow_Id;
            Writes_At_Least_One : Boolean := False;
            One_Is_Missing      : Boolean := False;
         begin
            for RC of Iter (Refinement_Constituents (E)) loop
               --  Check that at least one constituent is written
               if Nkind (RC) /= N_Null then
                  Constit := Direct_Mapping_Id (RC, Out_View);

                  if Actual_Writes.Contains (Constit) then
                     Writes_At_Least_One := True;
                  end if;

                  if not Actual_Writes.Contains (Constit) then
                     One_Is_Missing := True;
                  end if;
               end if;
            end loop;

            if Writes_At_Least_One
              and then One_Is_Missing
            then
               return True;
            end if;
         end;

         return False;
      end State_Partially_Written;

      -------------------------
      -- Up_Project_Flow_Set --
      -------------------------

      function Up_Project_Flow_Set
        (FS      : Flow_Id_Sets.Set;
         Variant : Flow_Id_Variant)
         return Flow_Id_Sets.Set
      is
         Up_Projected_Set : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

      begin
         for F of FS loop
            declare
               Elem : constant Flow_Id :=
                 (if Is_Non_Visible_Constituent (F, FA.S_Scope)
                  then Up_Project_Constituent (F, FA.S_Scope)
                  else F);
            begin
               Up_Projected_Set.Include (Change_Variant (Elem, Variant));
            end;
         end loop;

         return Up_Projected_Set;
      end Up_Project_Flow_Set;

   --  Start of processing for Check_Generated_Refined_Global

   begin
      Sane := True;

      if FA.Kind /= Kind_Subprogram
        or else No (FA.Global_N)
        or else not FA.Is_Generative
        or else Present (FA.Refined_Global_N)
        or else not Mentions_State_With_Visible_Refinement (FA.Global_N,
                                                            FA.B_Scope)
      then
         --  We have no work to do when:
         --
         --    1) we are not dealing with a subprogram
         --
         --    2) the user has not specified a Global aspect
         --
         --    3) there is a user-provided Refined_Global contract or the
         --       Global contract does not reference a state abstraction with
         --       visible refinement.
         return;
      end if;

      --  Read the Global contract (user globals)
      Get_Globals (Subprogram => FA.Analyzed_Entity,
                   Scope      => FA.S_Scope,
                   Classwide  => False,
                   Proof_Ins  => User_Proof_Ins,
                   Reads      => User_Reads,
                   Writes     => User_Writes);

      --  Read the Generated Globals (actual globals)
      Get_Globals (Subprogram => FA.Analyzed_Entity,
                   Scope      => FA.B_Scope,
                   Classwide  => False,
                   Proof_Ins  => Actual_Proof_Ins,
                   Reads      => Actual_Reads,
                   Writes     => Actual_Writes);

      --  Up project actual globals
      Projected_Actual_Writes    := Up_Project_Flow_Set (Actual_Writes,
                                                         Out_View);
      Projected_Actual_Reads     := Up_Project_Flow_Set (Actual_Reads,
                                                         In_View);
      Projected_Actual_Proof_Ins := Up_Project_Flow_Set (Actual_Proof_Ins,
                                                         In_View);

      --  Remove Reads from Proof_Ins
      Projected_Actual_Proof_Ins.Difference (Projected_Actual_Reads);

      --  Compare writes
      for W of Projected_Actual_Writes loop
         if not User_Writes.Contains (W) then
            Sane := False;

            Error_Msg_Flow
              (FA       => FA,
               Msg      => "& must be a global output of &",
               SRM_Ref  => "6.1.4",
               N        => FA.Global_N,
               Severity => Error_Kind,
               F1       => W,
               F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag      => Global_Missing);
         end if;
      end loop;

      for W of User_Writes loop
         declare
            E : constant Entity_Id := Get_Direct_Mapping_Id (W);
         begin
            if not Extended_Set_Contains (W, Projected_Actual_Writes) then
               --  Don't issue this error for state abstractions that have a
               --  null refinement.

               if Ekind (E) /= E_Abstract_State
                 or else Has_Non_Null_Refinement (E)
               then
                  Sane := False;

                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "global output & of & not written",
                     N        => FA.Global_N,
                     Severity => Error_Kind,
                     F1       => W,
                     F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                     Tag      => Global_Wrong);
               end if;

            elsif Ekind (E) = E_Abstract_State
              and then not User_Reads.Contains (Change_Variant (W, In_View))
              and then State_Partially_Written (W)
            then
               --  The synthesized Refined_Global is not fully written
               Sane := False;

               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "global output & of & not fully written",
                  N        => FA.Global_N,
                  Severity => Error_Kind,
                  F1       => W,
                  F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                  Tag      => Global_Wrong);
            end if;
         end;
      end loop;

      --  Compare reads
      for R of Projected_Actual_Reads loop
         if not User_Reads.Contains (R) then
            Sane := False;

            Error_Msg_Flow
              (FA       => FA,
               Msg      => "& must be a global input of &",
               SRM_Ref  => "6.1.4",
               N        => FA.Global_N,
               Severity => Error_Kind,
               F1       => R,
               F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag      => Global_Missing);
         end if;
      end loop;

      for R of User_Reads loop
         if not Extended_Set_Contains (R, Projected_Actual_Reads)
           and then not State_Partially_Written (R)
           --  Don't issue this error if we are dealing with a partially
           --  written state abstraction.
         then
            Sane := False;

            Error_Msg_Flow
              (FA       => FA,
               Msg      => "global input & of & not read",
               N        => FA.Global_N,
               Severity => Low_Check_Kind,
               F1       => R,
               F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag      => Global_Wrong);
         end if;
      end loop;

      --  Compare Proof_Ins
      for P of Projected_Actual_Proof_Ins loop
         if not User_Proof_Ins.Contains (P) then
            Sane := False;

            Error_Msg_Flow
              (FA       => FA,
               Msg      => "& must be a global Proof_In of &",
               SRM_Ref  => "6.1.4",
               N        => FA.Global_N,
               Severity => Error_Kind,
               F1       => P,
               F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag      => Global_Missing);
         end if;
      end loop;

      for P of User_Proof_Ins loop
         if not Extended_Set_Contains (P, Projected_Actual_Proof_Ins) then
            Sane := False;

            Error_Msg_Flow
              (FA       => FA,
               Msg      => "global Proof_In & of & not read",
               N        => FA.Global_N,
               Severity => Error_Kind,
               F1       => P,
               F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag      => Global_Wrong);
         end if;
      end loop;
   end Check_Generated_Refined_Global;

   -------------------
   -- Check_Part_Of --
   -------------------

   procedure Check_Part_Of
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean)
   is

      procedure Check (L : List_Id);
      --  We perform the check for the elements of a list L, which can be the
      --  list of either private or visible declarations of a package. In more
      --  detail: because we want to detect any non deferred constant with
      --  variable inputs declared immediately within the private part of a
      --  package or in the visible part of a package declared in the private
      --  part of another package, then, depending on these two cases, L will
      --  be:
      --  * the list of private declarations, if the package under analysis
      --    has a private part.
      --  * the list of visible declarations, if the package under analysis
      --    is present in the list of private declarations of another package.
      --
      --  For each element E of the list L, in case E is an object declaration
      --  we detect if it is a constant with variable input, if it is a package
      --  declaration we recursively check the same for each of its visible
      --  variables.

      procedure Detect_Constant_With_Variable_Input (E : Entity_Id);
      --  If entity E is a non deferred constant with variable input which does
      --  not have a Part_Of indicator then we issue an Error message.

      -----------
      -- Check --
      -----------

      procedure Check (L : List_Id)
      is
         N : Node_Id := First (L);
      begin
         while Present (N) loop
            case Nkind (N) is
               when N_Object_Declaration =>
                  --  N is an object declared immediately within the private
                  --  part and we detect if is a constant with variable input.

                  Detect_Constant_With_Variable_Input (Defining_Entity (N));

               when N_Package_Declaration =>
                  --  N is a package declared immediately within the private
                  --  part. If it is in SPARK, we recursively check its visible
                  --  declarations.

                  declare
                     Nested_Spec : constant Node_Id := Specification (N);

                  begin
                     if Entity_Spec_In_SPARK (Defining_Entity (N)) then
                        Check (Visible_Declarations (Nested_Spec));
                     end if;
                  end;

               when others =>
                  null;
            end case;

            Next (N);
         end loop;
      end Check;

      -----------------------------------------
      -- Detect_Constant_With_Variable_Input --
      -----------------------------------------

      procedure Detect_Constant_With_Variable_Input (E : Entity_Id)
      is
         function Is_Deferred_Constant (E : Entity_Id) return Boolean
         is (Is_Full_View (E) or else Present (Full_View (E)));
      begin
         if Ekind (E) = E_Constant
           and then Has_Variable_Input (E)
           and then not Present (Get_Pragma (E, Pragma_Part_Of))
           and then not Is_Deferred_Constant (E)
         then
            Sane := False;

            Error_Msg_Flow
              (FA       => FA,
               Msg      => "indicator Part_Of is required in this context: " &
                           "& is declared in the private part of package &",
               SRM_Ref  => "7.2.6(2)",
               N        => E,
               Severity => Error_Kind,
               F1       => Direct_Mapping_Id (E),
               F2       => Direct_Mapping_Id (FA.Spec_Entity));
         end if;
      end Detect_Constant_With_Variable_Input;

   --  Start of processing for Check_Part_Of

   begin
      Sane := True;

      --  We make sure we are looking at a package specification with a state
      --  abstraction otherwise the item cannot act as a Part_Of constituent.

      if Ekind (FA.Spec_Entity) = E_Package
        and then Present (Get_Pragma (FA.Spec_Entity, Pragma_Abstract_State))
      then
         Check (Private_Declarations (Package_Specification (FA.Spec_Entity)));
      end if;

   end Check_Part_Of;

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
