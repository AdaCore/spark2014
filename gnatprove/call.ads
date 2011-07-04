------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                                 C A L L                                  --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with GNAT.OS_Lib;       use GNAT.OS_Lib;
with String_Utils;      use String_Utils;

package Call is

   procedure Abort_With_Message (Msg : String);
   --  Print the Msg to Standard Error and Exit with Error code 1.

   procedure Call_Exit_On_Failure
     (Command   : String;
      Arguments : String_Lists.List;
      Success   : out Boolean;
      Verbose   : Boolean := False);
   --  Call the given command using the given argument list.
   --  Free all argument access values
   --  If the command exit status is not 0, print its output and exit.

   procedure Call_Exit_On_Failure
     (Command   : String;
      Arguments : Argument_List;
      Success   : out Boolean;
      Verbose   : Boolean := False);

   procedure Call_With_Status
     (Command   : String;
      Arguments : Argument_List;
      Status    : out Integer;
      Verbose   : Boolean := False);

   procedure Call_With_Status
     (Command   : String;
      Arguments : String_Lists.List;
      Status    : out Integer;
      Verbose   : Boolean := False);

   generic
      with procedure Handle_Line (Line : String);
   procedure For_Line_In_File
      (File : String);
   --  Do something for each line of a file.

   procedure Cat (File : String; Cut_Non_Blank_Line_At : Natural := 0);
   --  Print the file to stdout
end Call;
