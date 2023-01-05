------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                      F I L E C A C H E _ C L I E N T                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                        Copyright (C) 2022, AdaCore                       --
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

with Cache_Client; use Cache_Client;
with GNAT.OS_Lib;  use GNAT.OS_Lib;

package Filecache_Client is

   --  Package that implements a simple key/value cache using the file
   --  system. See the Cache_Client package for comments on the Set/Get/Close
   --  subprograms.

   type Filecache is new Cache with private;

   function Init (Dir : String) return Filecache;
   --  Create the file cache in directory Dir.

   overriding procedure Set (Conn : Filecache; Key : String; Value : String);

   overriding function Get (Conn : Filecache; Key : String) return String;

   overriding procedure Close (Conn : in out Filecache);

private

   type Filecache is new Cache with record
      Dir : String_Access;
   end record;

end Filecache_Client;
