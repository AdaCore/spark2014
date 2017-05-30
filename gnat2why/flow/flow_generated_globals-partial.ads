------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--        F L O W . G E N E R A T E D _ G L O B A L S . P A R T I A L       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2016-2017, Altran UK Limited              --
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
------------------------------------------------------------------------------

--  ### This generates globals (in phase 1). Package Phase_1 deals
--  with reading and writing to ALI files, but this is where the magic
--  happens.
--  ### Possibly rename after merge

package Flow_Generated_Globals.Partial is

   procedure Generate_Contracts (GNAT_Root : Node_Id);
   --  ??? perhaps this could be a library-level procedure and not a package

end Flow_Generated_Globals.Partial;
