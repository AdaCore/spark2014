------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Support, AIP.IPaddrs, AIP.Netbufs, AIP.Netconns;

use type AIP.S8_T;

package body NCO_Udpecho is

   procedure Run is
      NC : AIP.Netconns.Netconn_Id;
      NB : AIP.Netbufs.Netbuf_Id;
      IP : AIP.IPaddrs.IPaddr_Id;
      PT : AIP.U16_T;
      ER : AIP.Err_T;
   begin
      NC := AIP.Netconns.Netconn_New (AIP.Netconns.NETCONN_UDP);
      ER := AIP.Netconns.Netconn_Bind (NC, AIP.IPaddrs.IP_ADDR_ANY, 7);
      AIP.Support.Verify (ER = AIP.NOERR);

      while True loop
         NB := AIP.Netconns.Netconn_Recv (NC);
         IP := AIP.Netbufs.Netbuf_Fromaddr (NB);
         PT := AIP.Netbufs.Netbuf_Fromport (NB);

         ER := AIP.Netconns.Netconn_Connect (NC, IP, PT);
         AIP.Support.Verify (ER = AIP.NOERR);

         ER := AIP.Netconns.Netconn_Send (NC, NB);
         AIP.Support.Verify (ER = AIP.NOERR);

         AIP.Netbufs.Netbuf_Delete (NB);
      end loop;
   end Run;

end NCO_Udpecho;
