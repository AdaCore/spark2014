with AIP.Inet;

package body AIP.IPaddrs is

   function IP4 (A, B, C, D : AIP.U8_T) return IPaddr is
   begin
      return Inet.htonl
        (AIP.U32_T (A) * (2 ** 24)
         + AIP.U32_T (B) * (2 ** 16)
         + AIP.U32_T (C) * (2 ** 8)
         + AIP.U32_T (D));
   end IP4;

end AIP.IPaddrs;
