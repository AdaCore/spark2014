------------------------------------------------------------------------------
--                                                                          --
--                         GNAT LIBRARY COMPONENTS                          --
--                                                                          --
--    A D A . C O N T A I N E R S . B O U N D E D _ H A S H _ T A B L E S   --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--          Copyright (C) 2004-2008, Free Software Foundation, Inc.         --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 2,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT;  see file COPYING.  If not, write --
-- to  the  Free Software Foundation,  51  Franklin  Street,  Fifth  Floor, --
-- Boston, MA 02110-1301, USA.                                              --
--                                                                          --
-- As a special exception,  if other files  instantiate  generics from this --
-- unit, or you link  this unit with other files  to produce an executable, --
-- this  unit  does not  by itself cause  the resulting  executable  to  be --
-- covered  by the  GNU  General  Public  License.  This exception does not --
-- however invalidate  any other reasons why  the executable file  might be --
-- covered by the  GNU Public License.                                      --
--                                                                          --
-- This unit was originally developed by Matthew J Heaney.                  --
------------------------------------------------------------------------------

--  This package declares the hash-table type used to implement hashed
--  containers.

with Ada.Containers;
use Ada.Containers;

package Verified_Hash_Tables is
   pragma Pure;

   generic
      type Node_Type is private;

   package Generic_Hash_Table_Types is
      type Nodes_Type is array (Count_Type range <>) of Node_Type;
      type Buckets_Type is array (Hash_Type range <>) of Count_Type;

      type Hash_Table_Type
        (Capacity : Count_Type;
         Modulus  : Hash_Type)
      is tagged record
         Length  : Count_Type := 0;
         Busy    : Natural := 0;
         Lock    : Natural := 0;
         Free    : Count_Type;
         --  Find a way to lazy init this array ???
         Buckets : Buckets_Type (1 .. Modulus) := (others => 0);
         Nodes   : Nodes_Type (1 .. Capacity);
      end record;

      subtype Node_Access is Count_Type;
   end Generic_Hash_Table_Types;

end Verified_Hash_Tables;
