------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                              H A S H I N G                               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2015-2021, Altran UK Limited                --
--                     Copyright (C) 2015-2021, AdaCore                     --
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

--  This package is about hashing. We have a recurring need for this
--  throughout gnat2why and just doing the obvious conversions is not good
--  enough.

with Ada.Containers;

package Hashing with Pure is

   function Generic_Integer_Hash (N : Integer) return Ada.Containers.Hash_Type;
   pragma Inline (Generic_Integer_Hash);

end Hashing;
