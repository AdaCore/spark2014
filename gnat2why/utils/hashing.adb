------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                              H A S H I N G                               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2015-2019, Altran UK Limited                --
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

with Ada.Unchecked_Conversion;

package body Hashing is

   --------------------------
   -- Generic_Integer_Hash --
   --------------------------

   function Generic_Integer_Hash (N : Integer)
                                  return Ada.Containers.Hash_Type
   is
      function To_HT is
         new Ada.Unchecked_Conversion (Source => Integer,
                                       Target => Ada.Containers.Hash_Type);
   begin
      --  We can do something more clever here in the future.
      return To_HT (N);
   end Generic_Integer_Hash;

end Hashing;
