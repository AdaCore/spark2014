------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.Pbufs is

   procedure Pbuf_Blind_Free (Pb : Pbuf_Id) is
      N : AIP.U8_T;
      pragma Warnings (Off, N);
   begin
      N := Pbuf_Free (Pb);
   end Pbuf_Blind_Free;

end AIP.Pbufs;
