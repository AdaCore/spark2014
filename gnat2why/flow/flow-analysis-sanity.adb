------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . A N A L Y S I S . S A N I T Y                  --
--                                                                          --
--                                B o d y                                   --
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

--  This package implements a variety of sanity checks that are run before
--  the rest of flow analysis is performed.

with Sinfo;               use Sinfo;

with Why;
with Gnat2Why_Args;
with SPARK_Util;

with Flow_Error_Messages; use Flow_Error_Messages;
with Flow_Tree_Utility;   use Flow_Tree_Utility;
with Flow_Utility;        use Flow_Utility;

package body Flow.Analysis.Sanity is

   use type Flow_Graphs.Vertex_Id;
   use type Flow_Id_Sets.Set;

   ---------------------------------
   -- Check_Function_Side_Effects --
   ---------------------------------

   procedure Check_Function_Side_Effects
     (FA   : Flow_Analysis_Graphs;
      Sane : out Boolean)
   is
   begin
      Sane := True;

      if Ekind (FA.Analyzed_Entity) = E_Function
        and then FA.Function_Side_Effects_Present
      then
         if Gnat2Why_Args.Debug_Mode then
            Error_Msg_Flow
              (FA        => FA,
               Msg       => "flow analysis of & abandoned due to " &
                 "function with side effects",
               N         => FA.Analyzed_Entity,
               F1        => Direct_Mapping_Id (FA.Analyzed_Entity));
         end if;

         Sane := False;
      end if;
   end Check_Function_Side_Effects;

   --------------------
   -- Check_Aliasing --
   --------------------

   procedure Check_Aliasing
     (FA   : Flow_Analysis_Graphs;
      Sane : out Boolean)
   is
   begin
      Sane := True;

      if FA.Aliasing_Present then
         if Gnat2Why_Args.Debug_Mode then
            Error_Msg_Flow
              (FA        => FA,
               Msg       => "flow analysis of & abandoned due to aliasing",
               N         => FA.Analyzed_Entity,
               F1        => Direct_Mapping_Id (FA.Analyzed_Entity));
         end if;

         Sane := False;
      end if;
   end Check_Aliasing;

   -------------------------------------
   -- Check_Variable_Free_Expressions --
   -------------------------------------

   procedure Check_Variable_Free_Expressions
     (FA   : Flow_Analysis_Graphs;
      Sane : out Boolean)
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
                              Expand_Synthesized_Constants => True)));
      --  As above.

      -------------------------------------
      -- Check_Expressions_Variable_Free --
      -------------------------------------

      function Check_Expressions_Variable_Free
        (N : Node_Id) return Traverse_Result
      is
         ES1 : constant String := "default initialization ";
         ES2 : constant String := "subtype constraint ";
         ES3 : constant String := "cannot depend on &";
         ES4 : constant String := "renamed index ";
         ES5 : constant String := "renamed slice ";

         procedure Check_Flow_Id_Set
           (Flow_Ids : Ordered_Flow_Id_Sets.Set;
            Err_Msg  : String;
            Err_Node : Node_Id);
         --  Iterates over Flow_Ids. An error is issued for any member of
         --  that set which does NOT denote a constant.

         function Check_Name (N : Node_Id) return Traverse_Result;
         --  Checks indexed components and slices which are part of a Name
         --  subtree.

         -----------------------
         -- Check_Flow_Id_Set --
         -----------------------

         procedure Check_Flow_Id_Set
           (Flow_Ids : Ordered_Flow_Id_Sets.Set;
            Err_Msg  : String;
            Err_Node : Node_Id)
         is
         begin
            for F of Flow_Ids loop
               if (if F.Kind in Direct_Mapping | Record_Field
                   then not
                     (Is_Constant_Object (Get_Direct_Mapping_Id (F)) or
                        Is_Bound (F)))
               then
                  Error_Msg_Flow
                    (FA        => FA,
                     Msg       => Err_Msg,
                     SRM_Ref   => "4.4(2)",
                     N         => Err_Node,
                     F1        => F);
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
                                        Err_Msg  => ES4 & ES3,
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
                                        Err_Msg  => ES5 & ES3,
                                        Err_Node => Renamed_Slice);
                  end;

               when others =>
                  null;
            end case;

            return OK; -- Keep searching in case of nested prefixes
         end Check_Name;

         procedure Check_Name_Indexes_And_Slices is new
           Traverse_Proc (Check_Name);

      begin  --  Start of Check_Expressions_Variable_Free

         --  We do not sanity check any node which does not come from
         --  source. This way we ignore a number of issues related to
         --  compiler-generated types. See N116-011 for an example.

         if not Comes_From_Source (N) then
            return Skip;
         end if;

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

            when N_Loop_Parameter_Specification =>

               --  In a loop parameter specification, variables are allowed
               --  in the range constraint, so the tree walk is pruned here.

               return Skip;

            when N_Object_Renaming_Declaration =>
               Check_Name_Indexes_And_Slices (Name (N));
               return Skip;

            when N_Subtype_Indication =>
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
                                              Err_Msg  => ES2 & ES3,
                                              Err_Node => C);
                        end;

                        return Skip;

                     when N_Index_Or_Discriminant_Constraint =>
                        declare
                           Deps : constant Ordered_Flow_Id_Sets.Set :=
                             Simple_Variable_Set (Constraints (C));
                        begin
                           Check_Flow_Id_Set (Flow_Ids => Deps,
                                              Err_Msg  => ES2 & ES3,
                                              Err_Node => C);
                        end;

                        return Skip;

                     when N_Digits_Constraint |
                          N_Delta_Constraint =>

                        --  Ada LRM requires these constraints to be
                        --  static, so no further action required here.

                        return Skip;

                     when others =>
                        return OK;
                  end case;
               end;

            when N_Component_Declaration |
                 N_Discriminant_Specification =>

               if Present (Expression (N)) then
                  declare
                     Deps : constant Ordered_Flow_Id_Sets.Set :=
                       Simple_Variable_Set (Expression (N));
                  begin
                     Check_Flow_Id_Set (Flow_Ids => Deps,
                                        Err_Msg  => ES1 & ES3,
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

   begin
      Sane := True;

      --  Please don't try to simplify/delete Entry_Node here, it is also a
      --  global in Check_Expressions.

      case FA.Kind is
         when E_Subprogram_Body =>
            Entry_Node := SPARK_Util.Get_Subprogram_Body (FA.Analyzed_Entity);
            pragma Assert (Nkind (Entry_Node) = N_Subprogram_Body);
            Check_Expressions (Entry_Node);

         when E_Package =>
            Entry_Node := Get_Enclosing
              (FA.Analyzed_Entity, N_Package_Specification);
            Check_Expressions (Entry_Node);

         when E_Package_Body =>
            Entry_Node := Get_Enclosing
              (FA.Spec_Node, N_Package_Specification);
            Check_Expressions (Entry_Node);

            Entry_Node := Get_Enclosing (FA.Analyzed_Entity, N_Package_Body);
            Check_Expressions (Entry_Node);
      end case;

      if not Sane then
         if Gnat2Why_Args.Debug_Mode then
            Error_Msg_Flow
              (FA        => FA,
               Msg       => "flow analysis of & abandoned due to " &
                 "expressions with variable inputs",
               N         => FA.Analyzed_Entity,
               F1        => Direct_Mapping_Id (FA.Analyzed_Entity));
         end if;
      end if;
   end Check_Variable_Free_Expressions;

   -------------------------
   -- Check_Illegal_Reads --
   -------------------------

   procedure Check_Illegal_Reads
     (FA   : Flow_Analysis_Graphs;
      Sane : out Boolean)
   is
   begin
      Sane := True;

      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         if FA.PDG.Get_Key (V).Variant /= Final_Value then
            for R of FA.Atr.Element (V).Variables_Explicitly_Used loop
               case R.Kind is
                  when Direct_Mapping | Record_Field =>
                     if Ekind (Get_Direct_Mapping_Id (R)) =
                       E_Out_Parameter and then
                       Is_Volatile (R)
                     then
                        Error_Msg_Flow
                          (FA        => FA,
                           Msg       => "volatile formal out & cannot be read",
                           SRM_Ref   => "7.1.3(14)",
                           N         => Error_Location (FA.PDG, FA.Atr, V),
                           F1        => Entire_Variable (R));
                        Sane := False;
                     end if;

                  when Magic_String =>
                     --  Nothing to do in this case.
                     null;

                  when Null_Value | Synthetic_Null_Export =>
                     raise Why.Unexpected_Node;
               end case;
            end loop;
         end if;
      end loop;
   end Check_Illegal_Reads;

   --------------------------
   -- Check_Illegal_Writes --
   --------------------------

   procedure Check_Illegal_Writes
     (FA   : Flow_Analysis_Graphs;
      Sane : out Boolean)
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

               if not (FA.All_Vars.Contains (F) or Synthetic (F)) and
                 FA.Kind in E_Package | E_Package_Body
               then

                  --  We have a write to a variable a package knows
                  --  nothing about. This is always an illegal update.

                  case F.Kind is
                     when Direct_Mapping | Record_Field =>
                        Error_Msg_Flow
                          (FA        => FA,
                           Msg       => "cannot write & during " &
                             "elaboration of &",
                           SRM_Ref   => "7.7.1(5)",
                           N   => Error_Location (FA.PDG, FA.Atr, V),
                           F1  => Entire_Variable (Var),
                           F2  => Direct_Mapping_Id (FA.Analyzed_Entity));

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
                     if FA.Kind in E_Package | E_Package_Body then
                        Error_Msg_Flow
                          (FA        => FA,
                           Msg       => "cannot write & during " &
                             "elaboration of &",
                           SRM_Ref   => "7.7.1(5)",
                           N         => Error_Location (FA.PDG, FA.Atr, V),
                           F1        => Var,
                           F2        => Direct_Mapping_Id
                             (FA.Analyzed_Entity));

                     else
                        Error_Msg_Flow
                          (FA        => FA,
                           Msg       => "& must be a global output of &",
                           SRM_Ref   => "6.1.4",
                           N         => Error_Location (FA.PDG, FA.Atr, V),
                           F1        =>
                             (if A.Is_Parameter
                              then A.Parameter_Formal
                              else Var),
                           F2        => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Tag       => "illegal_update");
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
     (FA   : Flow_Analysis_Graphs;
      Sane : out Boolean)
   is
      Unused : Unbounded_String;
   begin
      Sane := True;

      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : constant V_Attributes := FA.Atr.Element (V);

            All_Vars : constant Ordered_Flow_Id_Sets.Set :=
              To_Ordered_Flow_Id_Set (A.Variables_Used or A.Variables_Defined);

            Aspect_To_Fix : constant String :=
              (case FA.Kind is
                  when E_Subprogram_Body =>
                    (if Present (FA.Refined_Global_N) then "Refined_Global"
                     elsif not Present (FA.Global_N) then "Depends"
                     else "Global"),
                  when others            => "Initializes");

            SRM_Ref : constant String :=
              (case FA.Kind is
                  when E_Subprogram_Body => "6.1.4(13)",
                  when others            => "7.1.5(12)");

            F : Flow_Id;
         begin
            for Var of All_Vars loop
               F := Change_Variant (Var, Normal_Use);

               if not (FA.All_Vars.Contains (F) or Synthetic (F)) then

                  --  Here we are dealing with a missing global

                  case F.Kind is
                     when Direct_Mapping | Record_Field =>
                        Error_Msg_Flow
                          (FA        => FA,
                           Msg       => "& must be listed in the " &
                             Aspect_To_Fix & " aspect of &",
                           SRM_Ref   => SRM_Ref,
                           N   => First_Variable_Use (FA      => FA,
                                                      Var     => Var,
                                                      Kind    => Use_Any,
                                                      Precise => False),
                           F1  => Entire_Variable (Var),
                           F2  => Direct_Mapping_Id (FA.Analyzed_Entity));

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

end Flow.Analysis.Sanity;
