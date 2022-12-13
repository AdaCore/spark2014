------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                          C A C H E _ C L I E N T                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                         Copyright (C) 2022, AdaCore                      --
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

package Cache_Client is

   type Cache is abstract tagged null record;
   --  Abstract type to represent a key/value cache.

   procedure Set (Conn : Cache; Key : String; Value : String) is abstract;
   --  Procedure to set the value of "Key" to "Value".

   function Get (Conn : Cache; Key : String) return String is abstract;
   --  Function to retrieve the value of "Key". If the key wasn't set
   --  previously, this function is intended to return the empty string.

   procedure Close (Conn : in out Cache) is abstract;
   --  Procedure to release any resources associated with the cache

end Cache_Client;
