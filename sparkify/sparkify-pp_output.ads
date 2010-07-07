------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                    S P A R K I F Y . P P _ O U T P U T                   --
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

--  This package defines the routines which send pieces of the special printed
--  source into the out stream.

with Asis;                       use Asis;
with Asis.Text;                  use Asis.Text;

with Sparkify.Cursors;           use Sparkify.Cursors;
with Sparkify.Basic;             use Sparkify.Basic;

package Sparkify.PP_Output is

   procedure PP_Close_Line (Increase_Count : Boolean := True);
   --  Closes the current output line by sending New_Line into the output
   --  stream. By default, this increases the count that stores at which input
   --  line this output line corresponds.

   procedure PP_Space;
   --  Send one space character into output stream.

   procedure PP_Pad (N : Natural);
   --  Sends N space characters into the output stream.

   procedure PP_Word (S : Program_Text);
   --  Send S into output stream.

   procedure PP_Word_Alone_On_Line (S : Program_Text);

   procedure PP_Word_Alone_On_Line_At
     (Column : Character_Position_Positive;
      S      : Program_Text);

   procedure PP_Keyword (KW : Keyword_Kinds);
   --  Sends the argument keyword in proper case into the output stream.
   --  Changes Line_Pos accordingly

   procedure PP_Delimiter (DL : Delimiter_Kinds);
   --  Sends the argument delimiter into the output stream. Changes Line_Pos
   --  accordingly

   procedure PP_Text_At
     (Line            : Line_Number_Positive;
      Column          : Character_Position_Positive;
      Text            : Asis.Program_Text;
      Prefix          : Wide_String := "";
      Keep_Only_Blank : Boolean := False);
   --  Sends Text to the output. If the current logical line is not Line, send
   --  first a line directive. If the current column is not Column, either pad
   --  the output with white space or start a new line, send a line directive
   --  and pad the output with white space to reach the appropriate column.

   procedure PP_Echo_Cursor_Range
     (From   : Cursor;
      To     : Cursor;
      Prefix : Wide_String := "");
   --  Echoes the input between cursors From and To

   procedure PP_Echo_And_Move_Cursor_Range
     (From   : in out Cursor;
      To     : Cursor;
      Prefix : Wide_String := "");
   --  Echoes the input between cursors From and To, and moves From after To

   procedure PP_Inherit
     (Line   : Line_Number_Positive;
      Column : Character_Position_Positive;
      Text   : Wide_String);
   --  Send Text into output stream as an inherit clause in SPARK syntax

   procedure PP_Check
     (Column : Character_Position_Positive;
      Exprs  : Asis.Expression_List);
   --  Send Expr into output stream as a check in SPARK syntax

   procedure PP_Assert
     (Line   : Line_Number_Positive;
      Column : Character_Position_Positive;
      Text   : Wide_String);
   --  Send Text into output stream as an assert in SPARK syntax

   procedure PP_Assert
     (Column : Character_Position_Positive;
      Exprs  : Asis.Expression_List);
   --  Send Expr into output stream as an assert in SPARK syntax

   procedure PP_Data_Flow
     (Column        : Character_Position_Positive;
      Global_In     : Wide_String;
      Global_Out    : Wide_String;
      Global_In_Out : Wide_String);
   --  Send globals into output stream as a data flow contract in SPARK syntax

   procedure PP_Package_State
     (Column      : Character_Position_Positive;
      Own         : Wide_String;
      Initializes : Wide_String);
   --  Send globals into output stream as a package state in SPARK syntax

   procedure PP_Precondition
     (Column : Character_Position_Positive;
      Exprs  : Asis.Expression_List);
   --  Send Expr into output stream as a precondition in SPARK syntax

   procedure PP_Postcondition
     (Is_Function : Boolean;
      Column      : Character_Position_Positive;
      Exprs       : Asis.Expression_List);
   --  Send Expr into output stream as a postcondition in SPARK syntax

   procedure PP_Line_Indication (Line : Line_Number);
   --  Outputs a special comment indicating a line number in the source file

   procedure PP_File_Indication (File : String);
   --  Outputs a special comment indicating a file name in the source file

end Sparkify.PP_Output;
