------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                              O U T P U T S                               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2021, AdaCore                     --
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

with Ada.Streams.Stream_IO; use Ada.Streams.Stream_IO;

package Outputs is
   --  This package provides some utilities to output indented text
   --  into a file.

   type Output_Record is limited private;
   --  An output record is a handle on an output file.
   --  It maintains an indentation level and offers ways to
   --  modify it and to write into its output file.

   procedure Open_Output
     (O        : in out Output_Record;
      Filename : String);
   --  Open Filename and set O's output to the corresponding file
   --  descriptor.

   procedure Close_Output (O : in out Output_Record);
   --  Close output O. After this operation, O shall not be used
   --  anymore.

   procedure Absolute_Indent (O : in out Output_Record; Level : Natural);
   --  Set the indentation level of O to Level

   procedure Relative_Indent (O : in out Output_Record; Diff : Integer);
   --  Increase the indentation level of O by Level (or decrease it
   --  if Level is lesser than zero).

   procedure P  (O : in out Output_Record; S : String);
   --  Put S to output O, indenting it if need be

   procedure PL (O : in out Output_Record; S : String);
   --  Put_Line S to output O, indenting it if need be

   procedure NL (O : in out Output_Record);
   --  Add a new line to output O; no trailing spaces are added
   --  even if the identation level is greater than zero.

   procedure Print_Box
     (O               : in out Output_Record;
      Subprogram_Name : String);
   --  Print a comment box of the form:
   --  ---------------------
   --  -- Subprogram_Name --
   --  ---------------------

   procedure Adjust_Columns
     (O        : in out Output_Record;
      Name_Len : Positive;
      Max_Len  : Positive);
   --  Print the correct number of space to align a declaration in
   --  a set of declarations. e.g
   --
   --  A    : T;    --  Max_Len = 4, Name_Len = 1, print 4 spaces
   --  AAAA : TTTT; --  Max_Len = 4, Name_Len = 4, print 1 space
   --  AA   : TT;   --  Max_Len = 4, Name_Len = 2, print 3 spaces

private

   type Output_Record is limited record
      File     : File_Type;
      --  Underlying file handle

      Indent   : Natural := 0;
      --  Indentation level

      New_Line : Boolean := False;
      --  Whether or not the last write in File created a new line;
      --  this is used to know if spaces should be written before
      --  the next P/PL operation (for indentation).
   end record;

end Outputs;
