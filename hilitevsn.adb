------------------------------------------------------------------------------
--                                                                          --
--                              HILITE COMPONENTS                           --
--                                                                          --
--                              H I L I T E V S N                           --
--                                                                          --
--                                   B o d y                                --
--                                                                          --
--                         Copyright (C) 2011-2013, AdaCore                 --
--                                                                          --
-- Hi-Lite is free software; you can redistribute it and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT; see file COPYING3.  If not, go to --
-- http://www.gnu.org/licenses for a complete copy of the license.          --
--                                                                          --
-- Hi-Lite is maintained by AdaCore (http://www.adacore.com)                --
--                                                                          --
------------------------------------------------------------------------------

package body Hilitevsn is

   ---------------------------
   -- Hilite_Version_String --
   ---------------------------

   function Hilite_Version_String return String is
   begin
      return Hilite_Static_Version_String;
   end Hilite_Version_String;

end Hilitevsn;
