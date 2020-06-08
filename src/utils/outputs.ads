------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                              O U T P U T S                               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

with Ada.Text_IO; use Ada.Text_IO;

package Outputs is
   --  This package provides some utilities to output indented text

   type Output_Id is (Stderr, Stdout, Current_File);
   --  Handle on an output. An indentation level is associated to each
   --  output; this package offers ways to modify this level and to write
   --  into the corresponding stream.

   procedure Open_Current_File (Filename : String);
   --  Open Filename and set current file's output to the corresponding file
   --  descriptor.

   procedure Close_Current_File;
   --  Close current file

   procedure Absolute_Indent (O : Output_Id; Level : Natural);
   --  Set the indentation level of O to Level

   procedure Relative_Indent (O : Output_Id; Diff : Integer);
   --  Increase the indentation level of O by Level (or decrease it
   --  if Level is lesser than zero).

   procedure P  (O : Output_Id; S : String; As_String : Boolean := False);
   --  Put S to output O, indenting it if need be. If As_String is true, the
   --  argument string is interpreted as a string literal.

   procedure PL (O : Output_Id; S : String);
   --  Put_Line S to output O, indenting it if need be

   procedure NL (O : Output_Id);
   --  Add a new line to output O; no trailing spaces are added
   --  even if the identation level is greater than zero.

private

   type Output_State is limited record
      Indent   : Natural := 0;
      --  Indentation level

      New_Line : Boolean := False;
      --  Whether or not the last write in File created a new line;
      --  this is used to know if spaces should be written before
      --  the next P/PL operation (for indentation).
   end record;

   Output_States : array (Output_Id) of Output_State;

   Current_File_Handle : File_Type;

end Outputs;
