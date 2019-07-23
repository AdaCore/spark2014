------------------------------------------------------------------------------
--                                                                          --
--                            SPARK 2014 COMPONENTS                         --
--                                                                          --
--                           S P A R K 2 0 1 4 V S N                        --
--                                                                          --
--                                   S p e c                                --
--                                                                          --
--                     Copyright (C) 2011-2019, AdaCore                     --
--                                                                          --
-- SPARK is free  software; you can redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT; see file COPYING3.  If not, go to --
-- http://www.gnu.org/licenses for a complete copy of the license.          --
--                                                                          --
------------------------------------------------------------------------------

package SPARK2014VSN is

   SPARK2014_Static_Version_String : constant String := "0.0w";
   --  Static string identifying this version, that can be used as an argument
   --  to e.g. pragma Ident.
   --
   --  WARNING: some scripts rely on the format of this string. Any change
   --  must be coordinated with the scripts requirements. Furthermore, no
   --  other variable in this package may have a name starting with
   --  SPARK2014_Static_Version.

   function SPARK2014_Version_String return String;
   --  Version output when SPARK 2014 related tools are run (with appropriate
   --  verbose option switch set).

end SPARK2014VSN;
