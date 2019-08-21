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

with Ada.Containers;
with Atree;                  use Atree;
with Einfo;                  use Einfo;
with Flow_Error_Messages;    use Flow_Error_Messages;
with Flow_Refinement;        use Flow_Refinement;
with Flow_Generated_Globals.Phase_2;
with Flow_Types;             use Flow_Types;
with Flow_Utility;           use Flow_Utility;
with Lib;                    use Lib;
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
         Reads, Writes : Flow_Id_Sets.Set;
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

         function To_Global (Var : Flow_Id) return Flow_Id;
         --  Converts Var from the fully-expanded proof view to what should
         --  appear in the Global contract.

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

            Partial, Projected : Flow_Id_Sets.Set;

            use type Ada.Containers.Count_Type;

         begin
            --  Convert from fully-expanded proof view to an object that is
            --  actually visible at the spec, e.g. from constituent to an
            --  abstract state.

            Up_Project (Flow_Id_Sets.To_Set (F),
                        Get_Flow_Scope (E),
                        Projected, Partial);

            --  The object has been either kept as it is (landing in Projected)
            --  or was a constituent that become an abstract state (landing in
            --  Partial).

            pragma Assert (Projected.Length + Partial.Length = 1);

            return (if Projected.Is_Empty
                    then Partial (Partial.First)
                    else Projected (Projected.First));
         end To_Global;

         --  Local constants:

         Error_Loc : constant Node_Id := Global_Pragma (E);

      --  Start of processing for Check_Incomplete_Globals

      begin
         --  ??? Once class-wide Global and Depends aspects are supported we
         --  can check the Pre'Class and Post'Class on abstract subprograms.

         if Is_Abstract_Subprogram (E) then
            return;
         end if;

         Get_Proof_Globals
           (Subprogram      => E,
            Reads           => Reads,
            Writes          => Writes,
            Erase_Constants => False,
            Scop            => Get_Flow_Scope (E));

         Proof_Context :=
           Reads
             or
           Writes
             or
           To_Flow_Id_Set (Get_Formals (E));

         --  For functions we also have the implicit 'Result object

         if Ekind (E) = E_Function then
            Proof_Context.Insert (Direct_Mapping_Id (E));
         end if;

         if Is_Expression_Function (E)
           or else (Ekind (E) = E_Function
                    and then Present (Get_Expression_Function (E))
                    and then Entity_Body_Compatible_With_SPARK (E))
         then
            for Var of Get_Vars (Expression (Get_Expression_Function (E))) loop
               if not Proof_Context.Contains (Var) then
                  Error_Msg_Flow (E          => E,
                                  Msg        => "& is referenced in " &
                                                "expression function " &
                                                "but missing from the Global",
                                  F1         => To_Global (Var),
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
                                  F1         => To_Global (Var),
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
                                  F1         => To_Global (Var),
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
           and then
             (Has_User_Supplied_Globals (E)
                or else
              (not Flow_Generated_Globals.Phase_2.GG_Has_Globals (E)
               and then not In_Predefined_Unit (E)))
         then
            Check_Incomplete_Global (E);
         end if;
      end loop;
   end Check_Incomplete_Globals;

end Flow_Sanity;
