------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System;
with Interfaces.C;

package Strings is
   function strlen (S : System.Address) return Interfaces.C.size_t;
   pragma Export (C, strlen, "strlen");

   function strncpy
     (Dest : System.Address;
      Src  : System.Address;
      N    : Interfaces.C.size_t) return System.Address;
   pragma Export (C, strncpy, "strncpy");
end Strings;
