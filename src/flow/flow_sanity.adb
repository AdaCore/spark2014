------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           F L O W . S A N I T Y                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2018-2025, Capgemini Engineering              --
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
with Einfo.Entities;         use Einfo.Entities;
with Einfo.Utils;            use Einfo.Utils;
with Errout_Wrapper;         use Errout_Wrapper;
with Flow_Error_Messages;    use Flow_Error_Messages;
with Flow_Refinement;        use Flow_Refinement;
with Flow_Generated_Globals.Phase_2;
with Flow_Types;             use Flow_Types;
with Flow_Utility;           use Flow_Utility;
with Sem_Aux;                use Sem_Aux;
with Sem_Util;               use Sem_Util;
with Sinfo.Nodes;            use Sinfo.Nodes;
with Snames;                 use Snames;
with SPARK_Definition;       use SPARK_Definition;
with SPARK_Util;             use SPARK_Util;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with Types;                  use Types;

package body Flow_Sanity is

   ------------------------------
   -- Check_Incomplete_Globals --
   ------------------------------

   procedure Check_Incomplete_Globals is

      procedure Check_Incomplete_Global (E : Entity_Id)
      with Pre => Ekind (E) in E_Entry | E_Function | E_Procedure;
      --  Check routine E for incomplete flow contract

      -----------------------------
      -- Check_Incomplete_Global --
      -----------------------------

      procedure Check_Incomplete_Global (E : Entity_Id) is
         procedure Check_Expr
           (Expr          : Node_Id;
            Proof_Context : Flow_Id_Sets.Set;
            Error_Loc     : Node_Id;
            Msg           : String)
         with Pre => Nkind (Expr) in N_Subexpr;
         --  Check expression Expr for references objects that are not in the
         --  Proof_Context and post message at Error_Loc using Msg for any
         --  violations.

         function Get_Vars (N : Node_Id) return Flow_Id_Sets.Set
         with Pre => Nkind (N) in N_Subexpr;
         --  Returns entire variables used in expression N

         function Global_Pragma (E : Entity_Id) return Node_Id
         with Post => Present (Global_Pragma'Result);
         --  Returns a pragma that acts as a source of the Global contract

         function To_Global (Var : Flow_Id) return Flow_Id;
         --  Converts Var from the fully-expanded proof view to what should
         --  appear in the Global contract.

         procedure Check_Expr
           (Expr          : Node_Id;
            Proof_Context : Flow_Id_Sets.Set;
            Error_Loc     : Node_Id;
            Msg           : String)
         is
            Unused : Boolean;
         begin
            for Var of Get_Vars (Expr) loop
               if not Proof_Context.Contains (Var) then
                  Error_Msg_Flow
                    (E          => E,
                     Msg        => Msg,
                     F1         => To_Global (Var),
                     Severity   => Error_Kind,
                     N          => Error_Loc,
                     Suppressed => Unused);
               end if;
            end loop;
         end Check_Expr;

         --------------
         -- Get_Vars --
         --------------

         function Get_Vars (N : Node_Id) return Flow_Id_Sets.Set is
         begin
            return Get_Variables_For_Proof (N, N);
         end Get_Vars;

         -------------------
         -- Global_Pragma --
         -------------------

         function Global_Pragma (E : Entity_Id) return Node_Id is
            N : Node_Id;
         begin
            N := Get_Pragma (E, Pragma_Global);

            if Present (N) then
               return N;
            end if;

            N := Get_Pragma (E, Pragma_Depends);

            if Present (N) then
               return N;
            end if;

            --  ??? now we should find the pragma Pure/Pure_Function that is
            --  implies Global => null, but apparently frontend does't provide
            --  a means for that.

            return Unit_Declaration_Node (E);
         end Global_Pragma;

         ---------------
         -- To_Global --
         ---------------

         function To_Global (Var : Flow_Id) return Flow_Id is
            F : constant Flow_Id :=
              (if Var.Kind = Magic_String
               then Get_Flow_Id (Var.Name)
               else Var);
            --  Proof view encodes entities not-in-SPARK and abstract states
            --  as Magic_String; convert them to flow view.

         begin
            --  Convert from fully-expanded proof view to an object that is
            --  actually visible at the spec, e.g. from constituent to an
            --  abstract state.

            return Up_Project (F, Get_Flow_Scope (E));
         end To_Global;

         --  Local variables

         Error_Loc : constant Node_Id := Global_Pragma (E);

         Reads, Writes : Flow_Id_Sets.Set;
         Proof_Context : Flow_Id_Sets.Set;
         --  Entities listed in the Global contract and formal parameters

         Unused : Boolean;

         use type Flow_Id_Sets.Set;

         --  Start of processing for Check_Incomplete_Globals

      begin
         Get_Proof_Globals
           (Subprogram      => E,
            Reads           => Reads,
            Writes          => Writes,
            Erase_Constants => False,
            Scop            => Get_Flow_Scope (E));

         Proof_Context := Reads or Writes or To_Flow_Id_Set (Get_Formals (E));

         --  For functions we also have the implicit 'Result object

         if Ekind (E) = E_Function then
            Proof_Context.Insert (Direct_Mapping_Id (E));
         end if;

         --  ??? Once class-wide Global and Depends aspects are supported we
         --  should check the Pre'Class and Post'Class against them. For now
         --  we check them against the implicit Global => null.

         if Is_Abstract_Subprogram (E) then
            pragma Assert (Reads.Is_Empty and then Writes.Is_Empty);

            for Pre of Get_Precondition_Expressions (E) loop
               Check_Expr
                 (Expr          => Pre,
                  Proof_Context => Proof_Context,
                  Error_Loc     => Error_Loc,
                  Msg           =>
                    "reference to global & in Pre'Class "
                    & "is not yet supported");
            end loop;

            for Post of Get_Postcondition_Expressions (E, Refined => False)
            loop
               Check_Expr
                 (Expr          => Post,
                  Proof_Context => Proof_Context,
                  Error_Loc     => Error_Loc,
                  Msg           =>
                    "reference to global & in Post'Class "
                    & "is not yet supported");
            end loop;

            return;
         end if;

         if Is_Expression_Function (E)
           or else (Is_Expression_Function_Or_Completion (E)
                    and then Entity_Body_Compatible_With_SPARK (E))
         then
            Check_Expr
              (Expr          => Expression (Get_Expression_Function (E)),
               Proof_Context => Proof_Context,
               Error_Loc     => Error_Loc,
               Msg           =>
                 "& is referenced in expression function "
                 & "but missing from the Global");
         end if;

         for Pre of Get_Precondition_Expressions (E) loop
            Check_Expr
              (Expr          => Pre,
               Proof_Context => Proof_Context,
               Error_Loc     => Error_Loc,
               Msg           =>
                 "& is referenced in Pre but missing from the Global");
         end loop;

         for Post of Get_Postcondition_Expressions (E, Refined => False) loop
            Check_Expr
              (Expr          => Post,
               Proof_Context => Proof_Context,
               Error_Loc     => Error_Loc,
               Msg           =>
                 "& is referenced in Post but missing from the Global");
         end loop;
      end Check_Incomplete_Global;

      --  Start of processing for Check_Incomplete_Globals

   begin
      for E of Entities_To_Translate loop
         if Ekind (E) in E_Entry | E_Function | E_Procedure
           and then (Has_User_Supplied_Globals (E)
                     or else (not Flow_Generated_Globals.Phase_2.GG_Has_Globals
                                    (E)
                              and then not Is_Ignored_Internal (E)))
           and then (if Ekind (E) = E_Function
                     then not Is_Predicate_Function (E))
         then
            Check_Incomplete_Global (E);
         end if;
      end loop;
   end Check_Incomplete_Globals;

end Flow_Sanity;
