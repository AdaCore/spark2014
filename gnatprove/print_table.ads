------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                           P R I N T _ T A B L E                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2016, AdaCore                   --
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

--  This package allows printing a text table which is nicely aligned.

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Text_IO;

package Print_Table with SPARK_Mode is
   Max_Size : constant Natural := 1000;

   type Alignment_Type is (Left_Align, Right_Align, Centered);

   type Cell is record
      Content : Unbounded_String;
      Align   : Alignment_Type;
   end record with
     Dynamic_Predicate => Length (Content) <= Max_Size;

   type Table_Content is array (Natural range <>, Natural range <>)
     of Cell;

   subtype Less_Than_Max_Size is Natural range 0 .. Max_Size;

   type Table (L, C : Less_Than_Max_Size) is record
      Content  : Table_Content (1 .. L, 1 .. C);
      Cur_Line : Positive;
      Cur_Col  : Positive;
   end record;

   function Create_Table (Lines, Cols : Natural) return Table
   with
     Global => null,
     Pre    => Lines <= Max_Size and Cols <= Max_Size;
   --  create a table and set the current cell to the upper-left cell.
   --  @param Lines
   --  @param Cols
   --  @return a table of size Lines x Cols

   procedure Put_Cell
     (T     : in out Table;
      S     : String;
      Align : Alignment_Type := Right_Align)
   with
     Global => null,
     Pre    => T.Cur_Line <= T.L and then T.Cur_Col <= T.C
     and then S'Length <= Max_Size;
   --  print a string into the current cell of the table, and move to the next
   --  cell. Note that this does not move to the next line, you need to call
   --  New_Line below after printing to the last cell of a line.
   --  @param T the table which contains the cell
   --  @param S the string to be put into the current cell
   --  @param Align the selected alignment for this cell

   procedure Put_Cell
     (T     : in out Table;
      S     : Natural;
      Align : Alignment_Type := Right_Align)
   with
     Global => null,
     Pre    => T.Cur_Line <= T.L and then T.Cur_Col <= T.C;
   --  same as Put_Cell for strings, but for numbers; if S is 0, prints a dot
   --  instead
   --  @param T the table which contains the cell
   --  @param S the number to be printed
   --  @param Align the selected alignment for this cell

   procedure New_Line (T : in out Table)
   with
     Global => null,
     Pre    => T.Cur_Col = T.C + 1 and then T.Cur_Line <= T.L;
   --  make sure that the current cell is the last cell of the line, and then
   --  set the current cell to the first cell of the next line
   --  @param T the table, this parameter is used only to check that the table
   --           has the expected number of columns.

   procedure Dump_Table (H : Ada.Text_IO.File_Type; T : Table)
   with
     Global => null;
   --  print the table T, nicely aligned, to the file H. The first line is
   --  considered a table header, so special markup is put there. Also, the
   --  last line is considered a summary, so special markup can apply.
   --  @param H the file handle to print the table to
   --  @param T the table to be dumped

end Print_Table;
