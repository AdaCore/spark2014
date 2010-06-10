------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.Pbufs is

   ------------------
   -- Pbuf_Release --
   ------------------

   procedure Pbuf_Release (Pb : Pbuf_Id)
   is
      N_Deallocs : AIP.U8_T := 0;
   begin
      --  Keep calling Pbuf_Free until it deallocates

      while N_Deallocs = 0 loop
         Pbuf_Free (Pb, N_Deallocs);
      end loop;
   end Pbuf_Release;

end AIP.Pbufs;
