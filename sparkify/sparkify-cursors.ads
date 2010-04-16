------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                     S P A R K I F Y . C U R S O R S                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2009-2010, AdaCore                     --
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

--  This package defines cursors in the current text file

with Asis;
with Asis.Text;                        use Asis.Text;

with Sparkify.Basic;                   use Sparkify.Basic;

package Sparkify.Cursors is

   type Cursor_Kind is
     (Before_File,       --  Represented as '---'
      After_File,        --  Represented as '+++'
      Before_Line,       --  Represented as '--'
      After_Line,        --  Represented as '++'
      Cursor_Column_Kind);

   --  Cursors of type Cursor_Column_Kind are further refined into 3 kinds.
   --  This indirection is needed to allow changing the column kind in place.

   type Column_Kind is
     (Before_Column,     --  Represented as '-'
      At_Column,         --  Represented as '*'
      After_Column);     --  Represented as '+'

   --  Type of cursor in the text file, represented pictorially as follows:
   --
   --      ---
   --          -----------
   --         |           |
   --         |           |
   --         |           |
   --      -- |  -[*]+    | ++
   --         |           |
   --          -----------
   --      +++
   --

   subtype Cursor_File_Kind is Cursor_Kind range Before_File .. After_File;
   subtype Cursor_Line_Kind is Cursor_Kind range Before_Line .. After_Line;

   subtype Line_Length is Natural range 0 .. 1000;

   type Cursor (Kind     : Cursor_Kind := Before_File;
                Line_Len : Line_Length := 0) is private;

   -------------
   -- Queries --
   -------------

   function Cursor_Line (C : Cursor) return Line_Number_Positive;
   --  Returns the corresponding line for C

   function Cursor_Column (C : Cursor) return Character_Position_Positive;
   --  Returns the corresponding column for C. If the cursor is not positioned
   --  on a real character in the file (e.g. line cursors), rounding is made
   --  towards the right. This corresponds to the column of the first character
   --  when printing from cursor C to another one.

   function Is_File_Cursor (C : Cursor) return Boolean;
   pragma Postcondition (Is_File_Cursor'Result = (C.Kind in Cursor_File_Kind));

   function Is_Line_Cursor (C : Cursor) return Boolean;
   pragma Postcondition (Is_Line_Cursor'Result = (C.Kind in Cursor_Line_Kind));

   function Is_Column_Cursor (C : Cursor) return Boolean;
   pragma Postcondition
     (Is_Column_Cursor'Result = (C.Kind = Cursor_Column_Kind));

   function Cursor_Has_Line (C : Cursor) return Boolean;
   pragma Postcondition (Cursor_Has_Line'Result = not Is_File_Cursor (C));

   function Cursor_On_Char (C : Cursor) return Boolean;
   --  Returns True if the cursor points to a character in the file. This is
   --  the case for cursors of kind At_Column, and those cursors of kind
   --  Before_Column and After_Column that do not point before or past the
   --  line.

   function Cursor_At_EOF (C : Cursor) return Boolean;
   --  Returns True if the cursor has reached the end-of-file

   function Cursor_Line_Range (From, To : Cursor) return Asis.Program_Text;
   pragma Precondition (Cursor_Line (From) = Cursor_Line (To));
   --  Return the image of the line range delimited by From and To

   -----------------
   -- Comparisons --
   -----------------

   function "=" (Left, Right : Cursor) return Boolean;
   --  Compares cursors Left and Right structurally. Column cursors pointing
   --  to the same column are recognized as equal even though they may not be
   --  of the same kind.

   function "<" (Left, Right : Cursor) return Boolean;
   --  Compares cursors Left and Right structurally. E.g., cursor Before_Line
   --  is considered to precede any cursor Before_Column on the same line,
   --  even when they refer to the same semantic location.

   function ">" (Left, Right : Cursor) return Boolean;
   --  Same as "<" with parameters reversed

   ------------------
   -- Constructors --
   ------------------

   function File_Cursor (Kind : Cursor_File_Kind) return Cursor;

   function Line_Cursor
     (Kind : Cursor_Line_Kind;
      Line : Line_Number_Positive) return Cursor;
   pragma Precondition (Line <= Lines_Table.Last);

   function Column_Cursor
     (Kind   : Column_Kind;
      Line   : Line_Number_Positive;
      Column : Character_Position_Positive) return Cursor;
   pragma Precondition (Line <= Lines_Table.Last);

   function Cursor_Before (Element : Asis.Element) return Cursor;
   --  Returns a cursor pointing just before Element

   function Cursor_At (Element : Asis.Element) return Cursor;
   --  Returns a cursor pointing at Element

   function Cursor_At_End_Of (Element : Asis.Element) return Cursor;
   --  Returns a cursor pointing at the end of Element

   function Cursor_After (Element : Asis.Element) return Cursor;
   --  Returns a cursor pointing just after Element

   function Max_Cursor (C1, C2 : Cursor) return Cursor;
   --  Returns the maximum of two cursors

   ---------------
   -- Modifiers --
   ---------------

   procedure Cursor_Next_Line (C : in out Cursor);
   --  Moves the cursor to the beginning of the line that follows, if any

   procedure Cursor_Next_Column (C : in out Cursor);
   --  When pointing to a column, move the cursor one column forward.
   --  Otherwise, do nothing.

   procedure Cursor_Move_Left (C : in out Cursor; N : Natural);
   pragma Precondition (Is_Column_Cursor (C));
   --  Moves the cursor N columns to the left if possible. Otherwise, aborts.

   procedure Skip_Blanks (C : in out Cursor);
   --  Moves the cursor forward to the first non-blank character (space, HT, FF
   --  and VT are blank characters), or to the end-of-file.

   procedure Skip_Word (C : in out Cursor; S : Asis.Program_Text);
   pragma Precondition (Is_Column_Cursor (C));
   --  Moves the cursor past the word given in argument. If this ends the line,
   --  the next line is pushed in the buffer.

private

   type Cursor (Kind     : Cursor_Kind := Before_File;
                Line_Len : Line_Length := 0) is record
      case Kind is
         when Cursor_File_Kind =>
            null;
         when others =>
            Line     : Line_Number_Positive;
            Line_Buf : Asis.Program_Text (1 .. Line_Len);
            --  The length of the line currently placed into the buffer
            --  (may be zero)
            case Kind is
               when Cursor_Column_Kind =>
                  Col_Kind : Column_Kind;
                  Column   : Character_Position_Positive;
               when others =>
                  null;
            end case;
      end case;
   end record;

end Sparkify.Cursors;
