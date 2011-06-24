------------------------------------------------------------------------------
--                                                                          --
--                              HILITE COMPONENTS                           --
--                                                                          --
--                              H I L I T E V S N                           --
--                                                                          --
--                                   S p e c                                --
--                                                                          --
--                         Copyright (C) 2011, AdaCore                      --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or modify it  --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnatprove is distributed in the hope that it will  be  useful,  --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- Hi-Lite is maintained by AdaCore (http://www.adacore.com)                --
--                                                                          --
------------------------------------------------------------------------------

package Hilitevsn is

   Hilite_Static_Version_String : constant String := "0.1";
   --  Static string identifying this version, that can be used as an argument
   --  to e.g. pragma Ident.
   --
   --  WARNING: some scripts rely on the format of this string. Any change
   --  must be coordinated with the scripts requirements. Furthermore, no
   --  other variable in this package may have a name starting with
   --  Hilite_Static_Version.

   function Hilite_Version_String return String;
   --  Version output when Hi-Lite related tools are run (with appropriate
   --  verbose option switch set).

end Hilitevsn;
