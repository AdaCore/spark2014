------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--         S P A R K I F Y . S O U R C E _ L I N E _ B U F F E R            --
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

--  This package defines basic manipulations on the cursor position inside the
--  buffer which holds the string image of the original source line. Skipping
--  some lexems might however cause the line in the buffer to change.

with Asis;

with Sparkify.Cursors;                 use Sparkify.Cursors;
with Sparkify.Basic;                   use Sparkify.Basic;

package Sparkify.Source_Line_Buffer is

   function Is_White_Text (Text : Asis.Program_Text) return Boolean;

   procedure Skip_Delimiter (C : in out Cursor; DL : Delimiter_Kinds);
   --  Moves the cursor past delimiter DL. If the next token is not equal to
   --  delimiter DL, raise an Assertion_Error.

   procedure Skip_Keyword (C : in out Cursor; KW : Keyword_Kinds);
   --  Moves the cursor past the keyword currently pointed at. If this ends
   --  the line, the next line is pushed in the buffer.

end Sparkify.Source_Line_Buffer;
