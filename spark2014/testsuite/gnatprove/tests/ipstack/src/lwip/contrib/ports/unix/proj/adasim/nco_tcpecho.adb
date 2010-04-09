------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System;
with AIP.Support, AIP.IPaddrs, AIP.Netbufs, AIP.Netconns;

package body NCO_Tcpecho is

   package SU renames AIP.Support;
   package NC renames AIP.Netconns;
   package NB renames AIP.Netbufs;

   use type NC.Netconn_Id;
   use type NB.Netbuf_Id;

   use type AIP.S8_T;

   procedure Run is

      LC, AC : NC.Netconn_Id;
      ER : AIP.Err_T;

      Nbu : NB.Netbuf_Id;
      Data : AIP.IPTR_T;
      Len : AIP.U16_T;
   begin
      LC := NC.Netconn_New (NC.NETCONN_TCP);

      --  Bind to port 77 instead of 7, to prevent conflict with
      --  an alternate server using the RAW api.

      ER := NC.Netconn_Bind (LC, AIP.IPaddrs.IP_ADDR_ANY, 77);
      SU.Verify (ER = AIP.NOERR);

      NC.Netconn_Listen (LC);

      while True loop

         AC := NC.Netconn_Accept (LC);

         if AC /= NC.NOCONN then

            loop
               Nbu := NC.Netconn_Recv (AC);
               exit when Nbu = NB.NOBUF;

               loop
                  NB.Netbuf_Data (Nbu, Data, Len);
                  ER := NC.Netconn_Write
                    (AC, Data, Len, NC.NETCONN_COPY);
                  exit when NB.Netbuf_Next (Nbu) < 0;
               end loop;

               NB.Netbuf_Delete (Nbu);
            end loop;

            NC.Netconn_Close (AC);
            NC.Netconn_Delete (AC);
         end if;

      end loop;
   end Run;

end NCO_Tcpecho;
