------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Support, AIP.IPaddrs, AIP.Netbufs, AIP.Netconns;

use type AIP.IPTR_T;
use type AIP.S8_T;

package body NCO_Tcpecho is

   procedure Run is

      LC, AC : AIP.Netconns.Netconn_Id;
      ER : AIP.Err_T;

      Nbu : AIP.Netbufs.Netbuf_Id;
      Data : AIP.IPTR_T;
      Len : AIP.U16_T;
   begin
      LC := AIP.Netconns.Netconn_New (AIP.Netconns.NETCONN_TCP);

      --  Bind to port 77 instead of 7, to prevent conflict with
      --  an alternate server using the RAW api.

      ER := AIP.Netconns.Netconn_Bind (LC, AIP.IPaddrs.IP_ADDR_ANY, 77);
      AIP.Support.Verify (ER = AIP.NOERR);

      AIP.Netconns.Netconn_Listen (LC);

      while True loop

         AC := AIP.Netconns.Netconn_Accept (LC);

         if AC /= AIP.Netconns.NOCONN then

            loop
               Nbu := AIP.Netconns.Netconn_Recv (AC);
               exit when Nbu = AIP.Netbufs.NOBUF;

               loop
                  AIP.Netbufs.Netbuf_Data (Nbu, Data, Len);
                  ER := AIP.Netconns.Netconn_Write
                    (AC, Data, Len, AIP.Netconns.NETCONN_COPY);
                  exit when AIP.Netbufs.Netbuf_Next (Nbu) < 0;
               end loop;

               AIP.Netbufs.Netbuf_Delete (Nbu);
            end loop;

            AIP.Netconns.Netconn_Close (AC);
            AIP.Netconns.Netconn_Delete (AC);
         end if;

      end loop;
   end Run;

end NCO_Tcpecho;
