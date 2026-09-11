------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--        F L O W . A N A L Y S I S . C O N T R A C T _ S A N I T Y         --
--                                                                          --
--                                B o d y                                   --
--                                                                          --
--                 Copyright (C) 2026, Capgemini Engineering                --
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

with Atree;                  use Atree;
with Errout_Wrapper;         use Errout_Wrapper;
with Flow_Error_Messages;    use Flow_Error_Messages;
with Flow_Utility;           use Flow_Utility;
with Sem_Util;               use Sem_Util;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with SPARK_Util.Types;       use SPARK_Util.Types;
with VC_Kinds;               use VC_Kinds;

package body Flow.Analysis.Contract_Sanity is

   -----------------------------------------
   -- Check_User_Defined_Equality_Globals --
   -----------------------------------------

   procedure Check_User_Defined_Equality_Globals (E : Entity_Id) is
   begin
      if not Is_User_Defined_Equality (E) or else not Is_Primitive (E) then
         return;
      end if;

      declare
         Scop : constant Flow_Scope := (Ent => E, Part => Visible_Part);
         --  We are looking from the subprogram spec

         Globals : Global_Flow_Ids;
         Unused  : Boolean;

      begin
         if Is_Nonlimited_Record_Type (Etype (First_Formal (E))) then
            Get_Globals
              (Subprogram => E,
               Scope      => Scop,
               Classwide  => False,
               Globals    => Globals);

            if not (Globals.Proof_Ins.Is_Empty
                    and then Globals.Inputs.Is_Empty)
            then
               Error_Msg_Flow
                 (E          => E,
                  Msg        =>
                    "user-defined equality shall "
                    & "have a Global aspect of null",
                  SRM_Ref    => "6.6(1)",
                  N          => E,
                  Severity   => Error_Kind,
                  Suppressed => Unused);
            end if;
         end if;
      end;
   end Check_User_Defined_Equality_Globals;

   ------------------------------------------
   -- Check_Inputs_Of_Contract_Expressions --
   ------------------------------------------

   procedure Check_Inputs_Of_Contract_Expressions (E : Entity_Id) is

      Scop : constant Flow_Scope := (Ent => E, Part => Visible_Part);
      --  We are looking from the subprogram spec

      Entry_Values : Flow_Id_Sets.Set;
      --  Objects that hold a meaningful value on entry to E

      Only_Outputs : Flow_Id_Sets.Set;
      --  Globals that the Global contract mentions, but only as outputs

      procedure Check_Expression (N : Node_Id; In_Old : Boolean)
      with Pre => Nkind (N) in N_Subexpr;
      --  Emit a message for every variable read by N that is not an input of
      --  E. In_Old tells whether N is the prefix of a 'Old, which only
      --  affects the wording.

      procedure Check_Old_Prefixes (N : Node_Id);
      --  Emit a message for every variable read by a 'Old prefix within N

      procedure Collect_Contract_Globals;
      --  Fill Entry_Values and Only_Outputs from the Global contract of E

      ----------------------
      -- Check_Expression --
      ----------------------

      procedure Check_Expression (N : Node_Id; In_Old : Boolean) is

         procedure Emit (Var : Flow_Id; Only_Output : Boolean);
         --  Report Var, which is read by N without being an input of E

         ----------
         -- Emit --
         ----------

         procedure Emit (Var : Flow_Id; Only_Output : Boolean) is
            Loc : constant Node_Id :=
              First_Variable_Use
                (N => N, Scope => Scop, Var => Var, Precise => False);

            Unused : Boolean;

         begin
            --  Use the same wording as the graph-based checks, so that a
            --  contract reads the same whether or not the body of E happens
            --  to be in SPARK.

            if Only_Output and then not In_Old then
               Error_Msg_Flow
                 (E             => E,
                  Msg           =>
                    "& is not an input in the "
                    & "Global contract of subprogram #",
                  Severity      => High_Check_Kind,
                  N             => Loc,
                  F1            => Var,
                  F2            => Direct_Mapping_Id (E),
                  Tag           => Uninitialized,
                  Suppressed    => Unused,
                  Continuations =>
                    [Create ("make it an input in the Global contract")]);
            else
               Error_Msg_Flow
                 (E          => E,
                  Msg        =>
                    (if In_Old
                     then "& is not initialized at subprogram entry"
                     else "& is not initialized"),
                  Severity   => High_Check_Kind,
                  N          => Loc,
                  F1         => Var,
                  Tag        => Uninitialized,
                  Suppressed => Unused);
            end if;
         end Emit;

      begin
         for F of
           Get_All_Variables
             (N                    => N,
              Scope                => Scop,
              Target_Name          => Null_Flow_Id,
              Use_Computed_Globals => True)
         loop
            declare
               Var : constant Flow_Id := Entire_Variable (F);

               Obj : constant Entity_Id :=
                 (if Var.Kind in Direct_Mapping | Record_Field
                  then Get_Direct_Mapping_Id (Var)
                  else Empty);
               --  Empty for an object known only by name, which comes from
               --  another compilation unit and so is never a formal of E

            begin
               --  Bounds, tags and input discriminants hold a meaningful
               --  value on entry even for an object which is not an input,
               --  unless they belong to a constituent of an abstract state.
               --  This mirrors the import status given to the initial
               --  vertices in Flow.Control_Flow_Graph.Utility.

               if (Is_Bound (F)
                   or else Is_Record_Tag (F)
                   or else Is_Input_Discriminant (F))
                 and then
                   not (Is_Constituent (F) or else Is_Implicit_Constituent (F))
               then
                  null;

               elsif Entry_Values.Contains (Var) then
                  null;

               --  A formal of E which is not an input is of mode out

               elsif Present (Obj)
                 and then Is_Formal (Obj)
                 and then Scope (Obj) = E
               then
                  Emit (Var, Only_Output => False);

               --  A global missing from the Global contract altogether is
               --  reported by Flow_Sanity.Check_Incomplete_Globals, and one
               --  is missing from Only_Outputs too when E has no Global
               --  contract at all, in which case its globals are only
               --  approximated and there is nothing to check against.

               elsif Only_Outputs.Contains (Var) then
                  Emit (Var, Only_Output => True);
               end if;
            end;
         end loop;
      end Check_Expression;

      ------------------------
      -- Check_Old_Prefixes --
      ------------------------

      procedure Check_Old_Prefixes (N : Node_Id) is

         function Check_Prefix (N : Node_Id) return Traverse_Result;

         ------------------
         -- Check_Prefix --
         ------------------

         function Check_Prefix (N : Node_Id) return Traverse_Result is
         begin
            if Is_Attribute_Old (N) then
               Check_Expression (N, In_Old => True);
            end if;

            return OK;
         end Check_Prefix;

         procedure Check_Prefix_Of_Attribute_Old is new
           Traverse_More_Proc (Process => Check_Prefix);

      begin
         Check_Prefix_Of_Attribute_Old (N);
      end Check_Old_Prefixes;

      ------------------------------
      -- Collect_Contract_Globals --
      ------------------------------

      procedure Collect_Contract_Globals is
         Globals : Global_Flow_Ids;

      begin
         Get_Globals
           (Subprogram => E,
            Scope      => Scop,
            Classwide  => False,
            Globals    => Globals);

         --  Get_Globals returns entire variables in the In_View and Out_View
         --  variants, while Get_All_Variables returns Normal_Use.

         for G of Globals.Inputs loop
            Entry_Values.Include (Change_Variant (G, Normal_Use));
         end loop;

         for G of Globals.Proof_Ins loop
            Entry_Values.Include (Change_Variant (G, Normal_Use));
         end loop;

         for G of Globals.Outputs loop
            declare
               Var : constant Flow_Id := Change_Variant (G, Normal_Use);
            begin
               if not Entry_Values.Contains (Var) then
                  Only_Outputs.Include (Var);
               end if;
            end;
         end loop;
      end Collect_Contract_Globals;

      Formal : Opt_Formal_Kind_Id;

   begin
      --  A task type has no contract expressions to check, and it is not an
      --  acceptable argument for Get_Precondition_Expressions

      if Ekind (E) = E_Task_Type then
         return;
      end if;

      --  The same defects are reported from the flow graph when we have one

      if Entity_Body_In_SPARK (E) then
         return;
      end if;

      Formal := First_Formal (E);
      while Present (Formal) loop
         if Ekind (Formal) in E_In_Parameter | E_In_Out_Parameter then
            Entry_Values.Include (Direct_Mapping_Id (Formal));
         end if;
         Next_Formal (Formal);
      end loop;

      --  Without an explicit Global contract the globals are approximated,
      --  from the contract expressions themselves for an imported subprogram
      --  and from the frontend cross-references otherwise, so there is
      --  nothing trustworthy to check the contract expressions against.

      if Has_User_Supplied_Globals (E) then
         Collect_Contract_Globals;
      end if;

      for Expr of Get_Precondition_Expressions (E) loop
         Check_Expression (Expr, In_Old => False);
      end loop;

      for Expr of Get_Postcondition_Expressions (E, Refined => False) loop
         Check_Old_Prefixes (Expr);
      end loop;
   end Check_Inputs_Of_Contract_Expressions;

end Flow.Analysis.Contract_Sanity;
