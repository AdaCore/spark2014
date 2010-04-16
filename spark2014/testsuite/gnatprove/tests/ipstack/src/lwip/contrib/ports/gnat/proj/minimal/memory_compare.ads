------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System; use System;
with Interfaces.C; use Interfaces.C;

package Memory_Compare is
pragma Preelaborate;

   function memcmp (S1 : Address; S2 : Address; N : size_t) return int;
   pragma Export (C, memcmp, "memcmp");
   --  compares the first n bytes of the memory areas s1 and s2.  It returns
   --  an integer less than, equal  to,  or  greater  than zero  if  s1  is
   --  found, respectively, to be less than, to match, or be greater than s2.

end Memory_Compare;
