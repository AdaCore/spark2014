------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . A N A L Y S I S . S A N I T Y                  --
--                                                                          --
--                                B o d y                                   --
--                                                                          --
--                  Copyright (C) 2013-2015, Altran UK Limited              --
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

with Ada.Containers;      use Ada.Containers;
with Elists;              use Elists;
with Flow_Error_Messages; use Flow_Error_Messages;
with Flow_Utility;        use Flow_Utility;
with Gnat2Why_Args;
with Sem_Aux;             use Sem_Aux;
with Sinfo;               use Sinfo;
with SPARK_Util;          use SPARK_Util;
with VC_Kinds;            use VC_Kinds;
with Why;

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
              (FA   => FA,
               Msg  => "flow analysis of & abandoned due to " &
                         "function with side effects",
               N    => FA.Analyzed_Entity,
               Kind => Error_Kind,
               F1   => Direct_Mapping_Id (FA.Analyzed_Entity));
         end if;

         Sane := False;
      end if;
   end Check_Function_Side_Effects;

   -------------------------------------
   -- Check_Variable_Free_Expressions --
   -------------------------------------

   procedure Check_Variable_Free_Expressions
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean)
   is
      Entry_Node : Node_Id;

      function Check_Expressions_Variable_Free
        (N : Node_Id) return Traverse_Result;
      --  Check that expressions used in certain contexts are free of
      --  variables, as per SPARK RM 4.4(2). This function deals with
      --  the following contexts:
      --     Component Declarations
      --     Discriminant Specifications
      --     Object Renaming Declarations

      function Simple_Variable_Set
        (N : Node_Id)
         return Ordered_Flow_Id_Sets.Set
      is
        (To_Ordered_Flow_Id_Set
           (Get_Variable_Set (N,
                              Scope                        => FA.B_Scope,
                              Local_Constants              =>
                                Node_Sets.Empty_Set,
                              Fold_Functions               => False,
                              Use_Computed_Globals         => True,
                              Expand_Synthesized_Constants => True)));
      --  A helpful wrapper around Get_Variable_Set as it is used in this
      --  sanity checking procedure.

      function Simple_Variable_Set
        (L : List_Id)
         return Ordered_Flow_Id_Sets.Set
      is
        (To_Ordered_Flow_Id_Set
           (Get_Variable_Set (L,
                              Scope                        => FA.B_Scope,
                              Local_Constants              =>
                                Node_Sets.Empty_Set,
                              Fold_Functions               => False,
                              Use_Computed_Globals         => True,
                              Expand_Synthesized_Constants => True)));
      --  As above.

      -------------------------------------
      -- Check_Expressions_Variable_Free --
      -------------------------------------

      function Check_Expressions_Variable_Free
        (N : Node_Id) return Traverse_Result
      is
         procedure Check_Flow_Id_Set
           (Flow_Ids : Ordered_Flow_Id_Sets.Set;
            Err_Desc : String;
            Err_Node : Node_Id);
         --  Iterates over Flow_Ids. An error is issued for any member of that
         --  set which does NOT denote a constant, a bound or a discriminant.

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
               if F.Kind in Direct_Mapping | Record_Field
                 and then Nkind (Get_Direct_Mapping_Id (F)) in N_Entity
                 and then not (Is_Constant_Object (Get_Direct_Mapping_Id (F))
                                 or else Is_Bound (F)
                                 or else Ekind (Get_Direct_Mapping_Id (F)) =
                                           E_Discriminant)
               then
                  Error_Msg_Flow
                    (FA      => FA,
                     Msg     => Err_Desc & " cannot depend on &",
                     SRM_Ref => "4.4(2)",
                     N       => Err_Node,
                     Kind    => Error_Kind,
                     F1      => F);
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
                     Renamed_Indexes : constant List_Id :=
                       Expressions (N);
                     Deps : constant Ordered_Flow_Id_Sets.Set :=
                       Simple_Variable_Set (Renamed_Indexes);
                  begin
                     Check_Flow_Id_Set (Flow_Ids => Deps,
                                        Err_Desc => "renamed index",
                                        Err_Node => N);
                  end;

               when N_Slice =>
                  declare
                     Renamed_Slice : constant Node_Id :=
                       Discrete_Range (N);
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

      --  Start of processing for Check_Expressions_Variable_Free

      begin
         case Nkind (N) is
            when N_Subprogram_Body |
                 N_Package_Specification |
                 N_Package_Body =>

               --  We do not want to process declarations of any nested
               --  subprograms or packages. These will be analyzed by their
               --  own pass of flow analysis.

               if N = Entry_Node then
                  return OK;
               else
                  return Skip;
               end if;

            when N_Full_Type_Declaration |
                 N_Subtype_Declaration   |
                 N_Private_Extension_Declaration =>
               declare
                  E          : constant Entity_Id := Defining_Identifier (N);
                  P          : constant Node_Id := Predicate_Function (E);
                  GP, GI, GO : Flow_Id_Sets.Set;
                  Deps       : Ordered_Flow_Id_Sets.Set;
               begin
                  if Present (P) then
                     Get_Globals (Subprogram => P,
                                  Scope      => FA.B_Scope,
                                  Classwide  => False,
                                  Proof_Ins  => GP,
                                  Reads      => GI,
                                  Writes     => GO);
                     pragma Assert (GO.Length = 0);
                     Deps := Ordered_Flow_Id_Sets.Empty_Set;
                     for F of GP loop
                        Deps.Insert (Change_Variant (F, Normal_Use));
                     end loop;
                     for F of GI loop
                        Deps.Insert (Change_Variant (F, Normal_Use));
                     end loop;
                     Check_Flow_Id_Set (Flow_Ids => Deps,
                                        Err_Desc => "predicate",
                                        Err_Node => E);
                  end if;
               end;
               return OK;

            when N_Loop_Parameter_Specification =>

               --  In a loop parameter specification, variables are allowed
               --  in the range constraint, so the tree walk is pruned here.

               return Skip;

            when N_Object_Renaming_Declaration =>
               Check_Name_Indexes_And_Slices (Name (N));
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
                           --  returns the union of the sets of the
                           --  low-bound and the high-bound.

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

                     when N_Digits_Constraint |
                          N_Delta_Constraint =>

                        --  Ada LRM requires these constraints to be
                        --  static, so no further action required here.

                        return Skip;

                     when others =>
                        raise Program_Error;
                  end case;
               end;

            when N_Component_Declaration      |
                 N_Discriminant_Specification =>

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
      end Check_Expressions_Variable_Free;

      procedure Check_Expressions is
        new Traverse_Proc (Check_Expressions_Variable_Free);

      Unused : Unbounded_String;

   --  Start of processing for Check_Variable_Free_Expressions

   begin
      Sane := True;

      --  Please don't try to simplify/delete Entry_Node here, it is also a
      --  global in Check_Expressions.

      case FA.Kind is
         when Kind_Subprogram =>
            Entry_Node := Subprogram_Body (FA.Analyzed_Entity);
            pragma Assert (Nkind (Entry_Node) = N_Subprogram_Body);
            Check_Expressions (Entry_Node);

         when Kind_Entry =>
            Entry_Node := Entry_Body (FA.Analyzed_Entity);
            Check_Expressions (Entry_Node);

         when Kind_Task =>
            Entry_Node := Task_Body (FA.Analyzed_Entity);
            Check_Expressions (Entry_Node);

         when Kind_Package =>
            Entry_Node := Package_Specification (FA.Analyzed_Entity);
            Check_Expressions (Entry_Node);

         when Kind_Package_Body =>
            Entry_Node := Package_Specification (FA.Spec_Entity);
            Check_Expressions (Entry_Node);

            Entry_Node := Package_Body (FA.Analyzed_Entity);
            Check_Expressions (Entry_Node);
      end case;

      if not Sane then
         if Gnat2Why_Args.Debug_Mode then
            Error_Msg_Flow
              (FA        => FA,
               Msg       => "flow analysis of & abandoned due to " &
                 "expressions with variable inputs",
               N         => FA.Analyzed_Entity,
               Kind      => Error_Kind,
               F1        => Direct_Mapping_Id (FA.Analyzed_Entity));
         end if;
      end if;
   end Check_Variable_Free_Expressions;

   --------------------------
   -- Check_Illegal_Writes --
   --------------------------

   procedure Check_Illegal_Writes
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean)
   is
      Unused : Unbounded_String;
   begin
      Sane := True;

      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : constant V_Attributes := FA.Atr.Element (V);

            Written_Vars : constant Ordered_Flow_Id_Sets.Set :=
              To_Ordered_Flow_Id_Set (A.Variables_Defined);

            F                    : Flow_Id;
            Corresp_Final_Vertex : Flow_Graphs.Vertex_Id;
            Final_Atr            : V_Attributes;
         begin
            for Var of Written_Vars loop
               F := Change_Variant (Var, Normal_Use);

               if not (FA.All_Vars.Contains (F) or else Synthetic (F)) and then
                 FA.Kind in Kind_Package | Kind_Package_Body
               then

                  --  We have a write to a variable a package knows
                  --  nothing about. This is always an illegal update.

                  case F.Kind is
                     when Direct_Mapping | Record_Field =>
                        Error_Msg_Flow
                          (FA      => FA,
                           Msg     => "cannot write & during " &
                             "elaboration of &",
                           SRM_Ref => "7.7.1(6)",
                           N       => Error_Location (FA.PDG, FA.Atr, V),
                           Kind    => Error_Kind,
                           F1      => Entire_Variable (Var),
                           F2      => Direct_Mapping_Id (FA.Analyzed_Entity));

                     when Magic_String =>
                        Global_Required (FA, Var);

                     when others =>
                        raise Program_Error;
                  end case;
                  Sane := False;

               elsif not FA.All_Vars.Contains (F) then

                  --  This case is dealt with in the "all_variables_known"
                  --  sanity check

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
                    and Final_Atr.Is_Constant
                    and not Final_Atr.Is_Loop_Parameter
                    and not Is_Abstract_State (Var)
                  then
                     if FA.Kind in Kind_Package | Kind_Package_Body then
                        Error_Msg_Flow
                          (FA      => FA,
                           Msg     => "cannot write & during " &
                                        "elaboration of &",
                           SRM_Ref => "7.7.1(6)",
                           N       => Error_Location (FA.PDG, FA.Atr, V),
                           Kind    => Error_Kind,
                           F1      => Var,
                           F2      => Direct_Mapping_Id (FA.Analyzed_Entity));

                     else
                        Error_Msg_Flow
                          (FA      => FA,
                           Msg     => "& must be a global output of &",
                           SRM_Ref => "6.1.4(16)",
                           N       => Error_Location (FA.PDG, FA.Atr, V),
                           Kind    => Error_Kind,
                           F1      => (if A.Is_Parameter
                                       then A.Parameter_Formal
                                       else Var),
                           F2      => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Tag     => Illegal_Update);
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
      Unused : Unbounded_String;

      function Find_Aspect_To_Fix return String;
      --  Returns a string that represents the aspect that needs to be
      --  corrected.

      ------------------------
      -- Find_Aspect_To_Fix --
      ------------------------

      function Find_Aspect_To_Fix return String is
      begin
         case FA.Kind is
            when Kind_Subprogram | Kind_Entry | Kind_Task =>
               if Present (FA.Refined_Global_N) then
                  return "Refined_Global";
               elsif Present (FA.Global_N) then
                  if Present (FA.Refined_Depends_N) then
                     return "Refined_Depends";
                  else
                     return "Global";
                  end if;
               elsif Present (FA.Depends_N) then
                  if Present (FA.Refined_Depends_N) then
                     return "Refined_Depends";
                  else
                     return "Depends";
                  end if;
               else
                  return "Global";
               end if;
            when Kind_Package | Kind_Package_Body  =>
               return "Initializes";
         end case;
      end Find_Aspect_To_Fix;

   --  Start of processing for Check_All_Variables_Known

   begin
      Sane := True;

      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : constant V_Attributes := FA.Atr.Element (V);

            All_Vars : constant Ordered_Flow_Id_Sets.Set :=
              To_Ordered_Flow_Id_Set (A.Variables_Used or A.Variables_Defined);

            Aspect_To_Fix : constant String := Find_Aspect_To_Fix;

            SRM_Ref : constant String :=
              (case FA.Kind is
               when Kind_Subprogram | Kind_Entry | Kind_Task => "6.1.4(13)",
               when Kind_Package | Kind_Package_Body         => "7.1.5(12)");

            F : Flow_Id;
         begin
            for Var of All_Vars loop
               F := Change_Variant (Var, Normal_Use);

               if not (FA.All_Vars.Contains (F) or Synthetic (F)) then

                  --  Here we are dealing with a missing global

                  case F.Kind is
                     when Direct_Mapping | Record_Field =>
                        Error_Msg_Flow
                          (FA      => FA,
                           Msg     => "& must be listed in the " &
                                        Aspect_To_Fix & " aspect of &",
                           SRM_Ref => SRM_Ref,
                           N       => First_Variable_Use (FA      => FA,
                                                          Var     => Var,
                                                          Kind    => Use_Any,
                                                          Precise => False),
                           F1      => (if Gnat2Why_Args.Flow_Advanced_Debug
                                       then Var
                                       else Entire_Variable (Var)),
                           Kind    => Error_Kind,
                           F2      => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Vertex  => V);

                     when Magic_String =>
                        Global_Required (FA, Var);

                     when others =>
                        raise Why.Unexpected_Node;
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
      --  Checks if F is either directly contained in FS or if F is a
      --  state abstraction that encloses an element of FS.
      --  The purpose of this function is to allow user contracts to
      --  mention either a state abstraction, or the constituents
      --  thereof when both are visible.
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

         --  Check if F is a state abstraction that encloses a
         --  constituent mentioned in FS.

         --  If F does not represent a state abstraction then return
         --  False.
         if not Is_Abstract_State (F) then
            return False;
         end if;

         declare
            State : constant Node_Id := Get_Direct_Mapping_Id (F);
         begin
            for Constit of FS loop
               if Constit.Kind in Direct_Mapping | Record_Field then
                  declare
                     N : constant Node_Id := Get_Direct_Mapping_Id (Constit);
                  begin
                     if Present (Encapsulating_State (N))
                       and then Encapsulating_State (N) = State
                     then
                        return True;
                     end if;
                  end;
               end if;
            end loop;
         end;

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
            Ptr                 : Elmt_Id;
            Constit             : Flow_Id;
            Writes_At_Least_One : Boolean := False;
            One_Is_Missing      : Boolean := False;
         begin
            Ptr := First_Elmt (Refinement_Constituents (E));
            while Present (Ptr) loop
               --  Check that at least one constituent is written
               if Nkind (Node (Ptr)) /= N_Null then
                  Constit := Direct_Mapping_Id (Node (Ptr), Out_View);

                  if Actual_Writes.Contains (Constit) then
                     Writes_At_Least_One := True;
                  end if;

                  if not Actual_Writes.Contains (Constit) then
                     One_Is_Missing := True;
                  end if;
               end if;

               Ptr := Next_Elmt (Ptr);
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
            if Is_Non_Visible_Constituent (F, FA.S_Scope) then
               declare
                  State : constant Flow_Id :=
                    Up_Project_Constituent (F, FA.S_Scope);
               begin
                  Up_Projected_Set.Include
                    (Change_Variant (State, Variant));
               end;
            else
               Up_Projected_Set.Include
                 (Change_Variant (F, Variant));
            end if;
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
         --    2) the user has not specified a Global aspect.
         --
         --    3) there is a user-provided Refined_Global contract
         --       or the Global contract does not reference a state
         --       abstraction with visible refinement.
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
      Projected_Actual_Proof_Ins := Projected_Actual_Proof_Ins -
                                      Projected_Actual_Reads;

      --  Compare writes
      for W of Projected_Actual_Writes loop
         if not User_Writes.Contains (W) then
            Sane := False;

            Error_Msg_Flow
              (FA      => FA,
               Msg     => "& must be a global output of &",
               SRM_Ref => "6.1.4",
               N       => FA.Global_N,
               Kind    => Error_Kind,
               F1      => W,
               F2      => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag     => Global_Missing);
         end if;
      end loop;

      for W of User_Writes loop
         declare
            E : constant Entity_Id := Get_Direct_Mapping_Id (W);
         begin
            if not Extended_Set_Contains (W, Projected_Actual_Writes) then
               --  Don't issue this error for state abstractions that
               --  have a null refinement.

               if Ekind (E) /= E_Abstract_State
                 or else Has_Non_Null_Refinement (E)
               then
                  Sane := False;

                  Error_Msg_Flow
                    (FA   => FA,
                     Msg  => "global output & of & not written",
                     N    => FA.Global_N,
                     Kind => Error_Kind,
                     F1   => W,
                     F2   => Direct_Mapping_Id (FA.Analyzed_Entity),
                     Tag  => Global_Wrong);
               end if;

            elsif Ekind (E) = E_Abstract_State
              and then not User_Reads.Contains (Change_Variant (W, In_View))
              and then State_Partially_Written (W)
            then
               --  The synthesized Refined_Global is not fully written
               Sane := False;

               Error_Msg_Flow
                 (FA   => FA,
                  Msg  => "global output & of & not fully written",
                  N    => FA.Global_N,
                  Kind => Error_Kind,
                  F1   => W,
                  F2   => Direct_Mapping_Id (FA.Analyzed_Entity),
                  Tag  => Global_Wrong);
            end if;
         end;
      end loop;

      --  Compare reads
      for R of Projected_Actual_Reads loop
         if not User_Reads.Contains (R) then
            Sane := False;

            Error_Msg_Flow
              (FA      => FA,
               Msg     => "& must be a global input of &",
               SRM_Ref => "6.1.4",
               N       => FA.Global_N,
               Kind    => Error_Kind,
               F1      => R,
               F2      => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag     => Global_Missing);
         end if;
      end loop;

      for R of User_Reads loop
         if not Extended_Set_Contains (R, Projected_Actual_Reads)
           and then not State_Partially_Written (R)
           --  Don't issue this error if we are dealing with a
           --  partially written state abstraction.
         then
            Sane := False;

            Error_Msg_Flow
              (FA   => FA,
               Msg  => "global input & of & not read",
               N    => FA.Global_N,
               Kind => Low_Check_Kind,
               F1   => R,
               F2   => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag  => Global_Wrong);
         end if;
      end loop;

      --  Compare Proof_Ins
      for P of Projected_Actual_Proof_Ins loop
         if not User_Proof_Ins.Contains (P) then
            Sane := False;

            Error_Msg_Flow
              (FA      => FA,
               Msg     => "& must be a global Proof_In of &",
               SRM_Ref => "6.1.4",
               N       => FA.Global_N,
               Kind    => Error_Kind,
               F1      => P,
               F2      => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag     => Global_Missing);
         end if;
      end loop;

      for P of User_Proof_Ins loop
         if not Extended_Set_Contains (P, Projected_Actual_Proof_Ins) then
            Sane := False;

            Error_Msg_Flow
              (FA   => FA,
               Msg  => "global Proof_In & of & not read",
               N    => FA.Global_N,
               Kind => Error_Kind,
               F1   => P,
               F2   => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag  => Global_Wrong);
         end if;
      end loop;
   end Check_Generated_Refined_Global;

end Flow.Analysis.Sanity;
