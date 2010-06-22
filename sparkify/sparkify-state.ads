------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                        S P A R K I F Y . S T A T E                       --
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

--  This package defines data which all together define the state of the
--  printer. Most of this data may be defined as the state of the traversal,
--  but we have only one traversal in Sparkify, and its state is rather
--  complicated, so we use global parameters to avoid passing complicated
--  structures as parameters of pre- and post-operations.

with Ada.Strings.Wide_Unbounded;       use Ada.Strings.Wide_Unbounded;

with GNAT.OS_Lib;                      use GNAT.OS_Lib;

package Sparkify.State is

   ---------------------
   -- Analysis Stages --
   ---------------------

   Before_CU         : Boolean := False;
   In_Context_Clause : Boolean := False;
   In_Unit           : Boolean := False;
   Behind_Unit       : Boolean := False;
   --  These boolean flags show where we are in the original source

   ------------------------
   -- Position in Output --
   ------------------------

   Output_Line       : Positive := 1;
   --  The (logical) number of the line in the output source

   Output_Column     : Positive := 1;
   --  The number of the column in the output source

   Output_Prefix     : Unbounded_Wide_String;
   --  The prefix of the current line in the output source

   -----------------------------
   -- File Processing Control --
   -----------------------------

   Arg_Source_Name   : String_Access;  --  ???
   Res_File_Name     : String_Access;

   Out_File_Exists   : Boolean := False;

   procedure Initialize;
   --  (Re)initialize the global variables declared in this package, needed in
   --  case of multiple file processing

end Sparkify.State;
