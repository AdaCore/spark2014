------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                                 C A L L                                  --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2025, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
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
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with GNAT.OS_Lib;   use GNAT.OS_Lib;
with GNATCOLL.JSON; use GNATCOLL.JSON;
with String_Utils;  use String_Utils;

package Call is

   Unproved_Checks_Error_Status : constant := 42;
   --  Error status to communicate from spark_report to gnatprove that some
   --  checks were not proved. An arbitrary value of 42 is picked.

   procedure Abort_With_Message (Msg : String) with
     No_Return;
   --  Print the Msg to Standard Error and Exit with Error code 1

   function Argument_List_Of_String_List (S : String_Lists.List)
      return Argument_List;
   --  Convert a String List into an Argument List

   procedure Call_With_Status
     (Command     : String;
      Arguments   : String_Lists.List;
      Status      : out Integer;
      Output_Name : String := "";
      Verbose     : Boolean := False);
   --  Call Command on Arguments, storing the output Status for the caller. If
   --  Output_Name is set to a non-empty string, both normal and error outputs
   --  are directed to that file. Otherwise, normal output is directed to
   --  Standout and error output is directed to Standerr. If Verbose is
   --  set, the command-line is displayed.

   function Read_File_Into_String (Fn : String) return String;
   --  Return a string with the contents of the file in argument.

   function Read_File_Into_JSON (Fn : String) return JSON_Value;
   --  Same as Read_File_Into_String, but directly parse the file into a JSON
   --  value. Works for large files as well.

   function Get_Process_Id return Integer;
   --  Return the process ID of the current process
   pragma Import (C, Get_Process_Id, "getpid");
   --  ??? Check if this works on windows

end Call;
