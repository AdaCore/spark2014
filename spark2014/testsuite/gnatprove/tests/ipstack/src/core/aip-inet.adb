------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.Inet is

   -----------
   -- htonl --
   -----------

   function htonl (V : AIP.U32_T) return AIP.U32_T is
      NetV : AIP.U32_T;
   begin
      --  Network byte ordering is big endian.  Swap value as needed.

      --# accept F, 22, "Value of expression is invariant";
      if AIP.HOST_BIG_ENDIAN then
      --# end accept;
         NetV := V;
      else
         NetV :=
           ((V and 16#FF#) * (2 ** 24))
           or ((V and 16#FF00#) * (2 ** 8))
           or ((V and 16#FF0000#) / (2 ** 8))
           or ((V and 16#FF000000#) / (2 ** 24));
      end if;

      return NetV;

   end htonl;

end AIP.Inet;
