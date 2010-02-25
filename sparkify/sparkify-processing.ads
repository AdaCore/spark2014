------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                   S P A R K I F Y . P R O C E S S I N G                  --
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

--  This package contains routines performing the main processing needed
--  by the special printer.

with Asis;

with ASIS_UL.Source_Table;             use ASIS_UL.Source_Table;

package Sparkify.Processing is

   procedure Special_Print (Unit : Asis.Compilation_Unit; SF : SF_Id);
   --  This is the ASIS special printer - it generates the modified source for
   --  Unit. SF is the index of the source file corresponding to this unit in
   --  Sparkify source table. We have placed this procedure into the spec to
   --  make it possible to use other drivers for the special printer.

end Sparkify.Processing;
