------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           F L O W . S A N I T Y                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2018-2019, Altran UK Limited                --
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
with Einfo;                  use Einfo;
with Flow_Error_Messages;    use Flow_Error_Messages;
with Flow_Refinement;        use Flow_Refinement;
with Flow_Types;             use Flow_Types;
with Flow_Utility;           use Flow_Utility;
with Sem_Aux;                use Sem_Aux;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
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
         Globals       : Global_Flow_Ids;
         Proof_Context : Flow_Id_Sets.Set;
         --  Entities listed in the Global contract and formal parameters

         Unused : Boolean;

         use type Flow_Id_Sets.Set;

         function Get_Vars (N : Node_Id) return Flow_Id_Sets.Set
         with Pre => Nkind (N) in N_Subexpr;
         --  Returns entire variables used in expression N

         function Global_Pragma (E : Entity_Id) return Node_Id
         with Post => Present (Global_Pragma'Result);
         --  Returns a pragma that acts as a source of the Global contract

         --------------
         -- Get_Vars --
         --------------

         function Get_Vars (N : Node_Id) return Flow_Id_Sets.Set is
         begin
            return
              To_Entire_Variables
                 (Get_Variables
                   (N,
                    Scope                => Get_Flow_Scope (E),
                    Fold_Functions       => False,
                    Use_Computed_Globals => True));
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

         --  Local constants:

         Error_Loc : constant Node_Id := Global_Pragma (E);

      --  Start of processing for Check_Incomplete_Globals

      begin
         Get_Globals (Subprogram => E,
                      Scope      => Get_Flow_Scope (E),
                      Classwide  => False,
                      Globals    => Globals);

         Proof_Context :=
           Change_Variant (Globals.Proof_Ins, Normal_Use)
             or
           Change_Variant (Globals.Inputs,    Normal_Use)
             or
           Change_Variant (Globals.Outputs,   Normal_Use)
             or
           To_Flow_Id_Set (Get_Formals (E));

         if Is_Expression_Function (E) then
            for Var of Get_Vars (Expression (Get_Expression_Function (E))) loop
               if not Proof_Context.Contains (Var) then
                  Error_Msg_Flow (E          => E,
                                  Msg        => "& is referenced in " &
                                                "expression function " &
                                                "but missing from the Global",
                                  F1         => Var,
                                  Severity   => Error_Kind,
                                  N          => Error_Loc,
                                  Suppressed => Unused);
               end if;
            end loop;

         end if;

         for Pre of Get_Precondition_Expressions (E) loop
            for Var of Get_Vars (Pre) loop
               if not Proof_Context.Contains (Var) then
                  Error_Msg_Flow (E          => E,
                                  Msg        => "& is referenced in Pre " &
                                                "but missing from the Global",
                                  F1         => Var,
                                  Severity   => Error_Kind,
                                  N          => Error_Loc,
                                  Suppressed => Unused);
               end if;
            end loop;
         end loop;

         for Post of Get_Postcondition_Expressions (E, Refined => False) loop
            for Var of Get_Vars (Post) loop
               if not Proof_Context.Contains (Var) then
                  Error_Msg_Flow (E          => E,
                                  Msg        => "& is referenced in Post " &
                                                "but missing from the Global",
                                  F1         => Var,
                                  Severity   => Error_Kind,
                                  N          => Error_Loc,
                                  Suppressed => Unused);
               end if;
            end loop;
         end loop;
      end Check_Incomplete_Global;

   --  Start of processing for Check_Incomplete_Globals

   begin
      for E of Entities_To_Translate loop
         if Ekind (E) in E_Entry | E_Function | E_Procedure
           and then Has_User_Supplied_Globals (E)
         then
            Check_Incomplete_Global (E);
         end if;
      end loop;
   end Check_Incomplete_Globals;

end Flow_Sanity;
