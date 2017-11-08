------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                                 C A L L                                  --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
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

with GNAT.OS_Lib;  use GNAT.OS_Lib;
with String_Utils; use String_Utils;

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

   procedure Free_Argument_List (L : Argument_List);
   --  free all strings in an argument list

   procedure Call_Exit_On_Failure
     (Command   : String;
      Arguments : String_Lists.List;
      Verbose   : Boolean := False);
   --  Call the given command using the given argument list.
   --  Free all argument access values.
   --  If the command exit status is not 0, print its output and exit.

   procedure Call_Exit_On_Failure
     (Command   : String;
      Arguments : Argument_List;
      Verbose   : Boolean := False);

   procedure Call_With_Status
     (Command   : String;
      Arguments : Argument_List;
      Status    : out Integer;
      Output_FD : File_Descriptor := Standout;
      Verbose   : Boolean := False;
      Free_Args : Boolean := True);

   function Call_With_Status
     (Command   : String;
      Arguments : String_Lists.List;
      Status    : out Integer;
      Verbose   : Boolean := False;
      Free_Args : Boolean := True)
      return String;
   --  Call Command on Arguments, returning both the Status of the system call,
   --  and the output on standard output as result.

   procedure Call_With_Status
     (Command   : String;
      Arguments : String_Lists.List;
      Status    : out Integer;
      Output_FD : File_Descriptor := Standout;
      Verbose   : Boolean := False;
      Free_Args : Boolean := True);

   function Get_Process_Id return Integer;
   --  Return the process ID of the current process
   pragma Import (C, Get_Process_Id, "getpid");

   generic
      with procedure Handle_Line (Line : String);
   procedure For_Line_In_File
      (File : String);
   --  Do something for each line of a file

   function Read_File_Into_String (Fn : String) return String;
   --  Return a string with the contents of the file in argument

   procedure Cat (File : String; Cut_Non_Blank_Line_At : Natural := 0);
   --  Print the file to stdout

   procedure Ch_Dir_Create_If_Needed (Dir : String);
   --  chdir to given directory; if it does not exist, create it before

end Call;
