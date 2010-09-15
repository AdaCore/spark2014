------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                        S P A R K I F Y . S T A T E                       --
--                                                                          --
--                                 B o d y                                  --
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

with Asis.Text;                        use Asis.Text;

with Sparkify.Basic;                   use Sparkify.Basic;

package body Sparkify.State is

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
   begin

      Before_CU         := False;
      In_Context_Clause := False;
      In_Unit           := False;
      Behind_Unit       := False;
      Output_Line       := 1;
      Output_Column     := 1;
      Arg_Source_Name   := null;
      Res_File_Name     := null;
      Out_File_Exists   := False;

   end Initialize;

   ----------------------------------
   -- Fill_Lines_Table_For_Element --
   ----------------------------------

   procedure Fill_Lines_Table_For_Element (Element : Asis.Element) is
      Full_Span : constant Asis.Text.Span := Compilation_Span (Element);
   begin
      --  Feeding the line table
      Lines_Table.Set_Last (Full_Span.Last_Line);
      Lines_Table.Table (1 .. Full_Span.Last_Line) :=
         Lines_Table.Table_Type
           (Lines (Element    => Element,
                   First_Line => Full_Span.First_Line,
                   Last_Line  => Full_Span.Last_Line));

      The_Last_Line   := Full_Span.Last_Line;
      The_Last_Column := Full_Span.Last_Column;
   end Fill_Lines_Table_For_Element;

end Sparkify.State;
