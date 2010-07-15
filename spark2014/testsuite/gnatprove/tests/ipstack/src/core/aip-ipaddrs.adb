------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.IPaddrs is

   ---------
   -- IP4 --
   ---------

   function IP4 (A, B, C, D : AIP.U8_T) return IPaddr is
   begin
      return
           AIP.M32_T (A) * 2**24
         + AIP.M32_T (B) * 2**16
         + AIP.M32_T (C) * 2**8
         + AIP.M32_T (D);
   end IP4;

   ---------
   -- Any --
   ---------

   function Any (IP : IPaddr) return Boolean is
   begin
      return IP = IP_ADDR_ANY;
   end Any;

   ----------
   -- Same --
   ----------

   function Same (IP1, IP2 : IPaddr) return Boolean is
   begin
      return IP1 = IP2;
   end Same;

   -----------
   -- Match --
   -----------

   function Match (IP1, IP2 : IPaddr) return Boolean is
   begin
      return Any (IP1) or else Any (IP2) or else Same (IP1, IP2);
   end Match;

end AIP.IPaddrs;
