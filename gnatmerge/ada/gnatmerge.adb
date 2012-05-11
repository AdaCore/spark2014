------------------------------------------------------------------------------
--                                                                          --
--                            G N A T M E R G E                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2012, AdaCore                       --
--                                                                          --
-- gnatmerge is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatmerge is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Text_IO;        use Ada.Text_IO;
with GNATCOLL.Scripts;   use GNATCOLL.Scripts;
with Common;             use Common;
with TextConsole;        use TextConsole;
with Configuration;      use Configuration;

procedure GNATMerge is
   Repo    : Scripts_Repository := Common.Register_Scripts_And_Functions;
   Buffer  : String (1 .. 1000);
   Last    : Integer;
   Errors  : Boolean;
   Console : aliased Text_Console;
   Script  : Scripting_Language := Lookup_Scripting_Language (Repo, "python");
begin
   Put_Line ("Look for python in " & Python_Dir);
   GNATCOLL.Scripts.Execute_File
     (Script   => Script,
      Filename => Public_API,
      Errors   => Errors);
   Put_Line ("Please type python commands:");

   Set_Default_Console (Script, Console'Unchecked_Access);

   loop
      Get_Line (Buffer, Last);
      Execute_Command
        (Script       => Lookup_Scripting_Language (Repo, "python"),
         Command      => Buffer (1 .. Last),
         Show_Command => False,
         Hide_Output  => False,
         Errors       => Errors);
   end loop;

exception
   when End_Error =>
      Destroy (Repo);
end GNATMerge;
