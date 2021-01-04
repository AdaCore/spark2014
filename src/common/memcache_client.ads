------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                       M E M C A C H E _ C L I E N T                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2017-2021, AdaCore                     --
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

with GNAT.Sockets; use GNAT.Sockets;

package Memcache_Client is

   --  Package that handles a connection and communication with a memcached
   --  server. Currently, only simple get and set operations are supported.

   type Cache_Connection is private;

   function Init (Hostname : String;
                  Port     : Port_Type) return Cache_Connection;
   --  @param Hostname hostname or IP address of a memcached server
   --  @param Port     port to connect to
   --  @return a connection object that can be used with the below get/set
   --    functions

   procedure Set (Conn  : Cache_Connection;
                  Key   : String;
                  Value : String);
   --  @param Conn a connection object to a memcached server
   --  @param Key the key for the data to be stored
   --  @param Value the value to be cached

   function Get (Conn : Cache_Connection;
                 Key  : String) return String;
   --  @param Conn a connection object to a memcached server
   --  @param Key the key for the data to be retrieved
   --  @return the value stored in the server for Key or empty if no value is
   --    stored

   procedure Close (Conn : in out Cache_Connection);
   --  @param Conn the connection to be closed

private

   type Cache_Connection is record
      Sock   : Socket_Type;
      Stream : Stream_Access;
   end record;

end Memcache_Client;
