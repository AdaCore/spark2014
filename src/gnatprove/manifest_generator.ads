------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                  M A N I F E S T _ G E N E R A T O R                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2026, AdaCore                          --
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

with Gnatprove_Build;

package Manifest_Generator is

   procedure Generate (Units : Gnatprove_Build.Unit_Set; Output_Dir : String);
   --  Generate one proof manifest TOML file per unit in Units, deriving each
   --  unit's .spark file and skipping the units whose file does not exist.
   --  The manifests are written into Output_Dir. Each generated file is named
   --  after the Ada name of the unit (and entities are attributed to it)
   --  rather than after the source file, so generation works also under a
   --  non-default naming scheme.

end Manifest_Generator;
