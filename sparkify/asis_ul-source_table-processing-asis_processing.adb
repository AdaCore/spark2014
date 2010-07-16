------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--     A S I S _ U L . S O U R C E _ T A B L E . P R O C E S S I N G .      --
--                      A S I S _ P R O C E S S I N G                       --
--                                                                          --
--             (adapted for sparkify from ASIS Utility Library)             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- Sparkify is  free  software;  you can redistribute it  and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. Sparkify is distributed in the hope that it will be useful, but --
-- WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHANTABI- --
-- LITY or  FITNESS  FOR A  PARTICULAR  PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- Sparkify is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Characters.Handling;          use Ada.Characters.Handling;

with Asis.Elements;                    use Asis.Elements;

with ASIS_UL.Global_State.CG;

with Sparkify.Output;
with Sparkify.Processing;
with Sparkify.Common;                  use Sparkify.Common;
with Sparkify.Names;                   use Sparkify.Names;
with Sparkify.Basic;                   use Sparkify.Basic;

separate (ASIS_UL.Source_Table.Processing)
procedure ASIS_Processing (CU : Asis.Compilation_Unit; SF : SF_Id) is
   Unit : constant Asis.Element := Unit_Declaration (CU);
   Success : Boolean;

   function To_Lower (S : Wide_String) return String;

   function To_Lower (S : Wide_String) return String is
   begin
      return To_Lower (Ada.Characters.Conversions.To_String (S));
   end To_Lower;

begin
   case Current_Pass is
      when Effects =>
         ASIS_UL.Global_State.CG.Collect_CG_Info_From_Construct (Unit);
         Set_Source_Status (SF, Processed);
      when Printing_Data =>
         case Declaration_Kind (Unit) is
            when A_Package_Declaration |
                 A_Generic_Package_Declaration =>
               Set_Current_SF (SF);
               Sparkify.Output.Set_Output (SF, "", Success);
               Sparkify.Processing.Special_Print (CU, SF);
            when A_Package_Body_Declaration |
                 A_Procedure_Body_Declaration |
                 A_Procedure_Declaration |
                 A_Function_Body_Declaration |
                 A_Function_Declaration =>
               --  Do not print the body of the external package
               Set_Source_Status (SF, Processed);
            when others =>
               raise Not_Implemented_Yet;
         end case;
      when Printing_External =>
         case Declaration_Kind (Unit) is
            when A_Package_Declaration |
                 A_Generic_Package_Declaration =>
               Set_Current_SF (SF);
               Sparkify.Output.Set_Output
                 (SF, To_Lower (External_Prefix), Success);
               Sparkify.Processing.Special_Print (CU, SF);
            when A_Package_Body_Declaration |
                 A_Procedure_Body_Declaration |
                 A_Procedure_Declaration |
                 A_Function_Body_Declaration |
                 A_Function_Declaration =>
               --  Do not print the body of the external package
               Set_Source_Status (SF, Processed);
            when others =>
               raise Not_Implemented_Yet;
         end case;
      when Printing_Internal =>
         Set_Current_SF (SF);
         Sparkify.Output.Set_Output (SF, To_Lower (Internal_Prefix), Success);
         Sparkify.Processing.Special_Print (CU, SF);
   end case;

end ASIS_Processing;
