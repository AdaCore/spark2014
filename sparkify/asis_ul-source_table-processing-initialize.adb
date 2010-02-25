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

with Sparkify.Basic;                   use Sparkify.Basic;
with Sparkify.Options;                 use Sparkify.Options;
with Sparkify.Output;                  use Sparkify.Output;
with Sparkify.State;                   use Sparkify.State;

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
end Initialize;
