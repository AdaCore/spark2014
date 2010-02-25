------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                       S P A R K I F Y . O U T P U T                      --
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

--  This package defines various output routines

with ASIS_UL.Source_Table;             use ASIS_UL.Source_Table;

package Sparkify.Output is

   procedure Set_Output (SF : SF_Id; Success : out Boolean);
   --  Creates or opens, if needed, and sets the output file for SF, depending
   --  on sparkify options. Success is set ON if the output file has been
   --  successfully opened, and OFF otherwise

   procedure Brief_Help;
   --  Prints the brief help into the error stream.

   function PP_Suffix  return String;
   function NPP_Suffix return String;
   --  These functions return suffixes for the file names for default result
   --  and backup copy files. ('.pp' and '.npp' for all hosts but OpenVMS and
   --  '$PP' and '$NPP' for OpenVMS

   Out_Dirname : constant String := "sparkified";
   --  Name of the output directory where output files should be created

   procedure Set_Form_String;
   --  Sets the value used for the Form parameter of Create and Open
   --  procedures, this value defines the encoding used for the output file(s).

   procedure Correct_EOL;
   --  This is a text filter procedure that converts the line end format of the
   --  result file to the format set by Sparkify.Options.Out_File_Format.

end Sparkify.Output;
