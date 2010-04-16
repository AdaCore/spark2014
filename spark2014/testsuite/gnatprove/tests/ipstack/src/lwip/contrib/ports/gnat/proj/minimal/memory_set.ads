------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System; use System;
with Interfaces.C; use Interfaces.C;

package Memory_Set is
   pragma Preelaborate;

   function Memset (M : Address; C : int; Size : size_t) return Address;
   pragma Export (C, Memset, "memset");
   --  This function stores C converted to a Character in each of the elements
   --  of the array of Characters beginning at M, with size Size. It returns a
   --  pointer to M.

end Memory_Set;
