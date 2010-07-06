------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--     A S I S _ U L . S O U R C E _ T A B L E . P R O C E S S I N G .      --
--                           I N I T I A L I Z E                            --
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

with Ada.Wide_Text_IO;

with ASIS_UL.Environment;              use ASIS_UL.Environment;
with ASIS_UL.Options;
with ASIS_UL.Global_State.CG;

with Sparkify.Basic;                   use Sparkify.Basic;
with Sparkify.Options;                 use Sparkify.Options;
with Sparkify.Output;                  use Sparkify.Output;
with Sparkify.State;                   use Sparkify.State;
with Sparkify.Common;                  use Sparkify.Common;

separate (ASIS_UL.Source_Table.Processing)
procedure Initialize is
begin
   if not ASIS_UL.Options.Nothing_To_Do
     and then
      Output_Mode in Replace .. Replace_No_Backup
   then

      Res_File_Name := new String'(Temp_Dir.all & PP_Suffix);

      Ada.Wide_Text_IO.Create (File => Result_Out_File,
                               Mode => Ada.Wide_Text_IO.Out_File,
                               Name => Res_File_Name.all,
                               Form => Form_String.all);

      Ada.Wide_Text_IO.Close (File => Result_Out_File);

      Out_File_Exists := True;
   end if;

   --  HACK: perform a first pass over the AST in the initialization for the
   --  second pass. This should be removed as soon as a multi-pass API is
   --  available.

   Current_Pass := Effects;
   ASIS_UL.Global_State.Initialize;
   ASIS_UL.Global_State.Do_Compute_Global_Objects_Accessed;
   ASIS_UL.Source_Table.Processing.Process_Sources;
   ASIS_UL.Global_State.CG.Transitive_Closure;
   --  Globally reset all status flags to Waiting
   for SF in First_SF_Id .. SF_Id (Natural (First_SF_Id) + Total_Sources) loop
      if Present (SF) then
         Set_Source_Status (SF, Waiting);
      end if;
   end loop;
   --  Reinitialize Sources_Left
   Sources_Left := Total_Sources;

   --  HACK: perform a second pass over the AST in the initialization for the
   --  third pass. This should be removed as soon as a multi-pass API is
   --  available.

   Current_Pass := Printing_Data;
   ASIS_UL.Source_Table.Processing.Process_Sources;
   --  Globally reset all status flags to Waiting
   for SF in First_SF_Id .. SF_Id (Natural (First_SF_Id) + Total_Sources) loop
      if Present (SF) then
         Set_Source_Status (SF, Waiting);
      end if;
   end loop;
   --  Reinitialize Sources_Left
   Sources_Left := Total_Sources;

   --  HACK: perform a third pass over the AST in the initialization for the
   --  fourth pass. This should be removed as soon as a multi-pass API is
   --  available.

   Current_Pass := Printing_External;
   ASIS_UL.Source_Table.Processing.Process_Sources;
   --  Globally reset all status flags to Waiting
   for SF in First_SF_Id .. SF_Id (Natural (First_SF_Id) + Total_Sources) loop
      if Present (SF) then
         Set_Source_Status (SF, Waiting);
      end if;
   end loop;
   --  Reinitialize Sources_Left
   Sources_Left := Total_Sources;

   --  Set the mode for the fourth pass

   Current_Pass := Printing_Internal;

end Initialize;
