------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             G N A T 2 W H Y                              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Command_Line; use Ada.Command_Line;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Ada.Directories; use Ada.Directories;
with GNAT.IO; use GNAT.IO;
with GNAT.OS_Lib; use GNAT.OS_Lib;
with GNAT.Strings;
with GNAT.Directory_Operations; use GNAT.Directory_Operations;

--  Wrapper around gcc -c -x adawhy to provide a gnatwhy executable.

procedure GNAT2Why_Wrapper is

   Debug : constant Boolean := False;

   function Locate_Exec (Exec : String) return String_Access;
   --  Locate Exec either from argv(0) or from the PATH.

   -----------------
   -- Locate_Exec --
   -----------------

   function Locate_Exec (Exec : String) return String_Access is
      Command     : constant String := Command_Name;
      Exe         : String_Access := Get_Target_Executable_Suffix;
      Exec_Suffix : constant String := Exe.all;

   begin
      Free (Exe);

      if Is_Absolute_Path (Command)
        and then Is_Executable_File (Compose
                   (Containing_Directory (Command), Exec & Exec_Suffix))
      then
         return new String'(Compose (Containing_Directory (Command), Exec));
      else
         return Locate_Exec_On_Path (Exec);
      end if;
   end Locate_Exec;

   Count          : constant Natural := Argument_Count;
   Args           : Argument_List (1 .. Count + 3);
   Exec           : String_Access;
   Status         : Integer;

begin
   Args (1) := new String'("-c");
   Args (2) := new String'("-x");
   Args (3) := new String'("adawhy");

   for J in 1 .. Count loop
      Args (J + 3) := new String'(Argument (J));
   end loop;

   if Debug then
      Put ("gcc");

      for J in Args'Range loop
         Put (" " & Args (J).all);
      end loop;

      New_Line;
   end if;

   Exec := Locate_Exec ("gcc");

   if Exec = null then
      Put_Line ("gcc executable not found, exiting.");
      OS_Exit (1);
   end if;

   Status := Spawn (Exec.all, Args);

   for J in Args'Range loop
      Free (Args (J));
   end loop;

   Free (Exec);
   OS_Exit (Status);
end GNAT2Why_Wrapper;
