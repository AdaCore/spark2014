------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System;
with AIP_Ctypes, AIP_IPaddrs, AIP_Netbufs, AIP_Netconns;

package body AIP_Tcpecho is

   use type AIP_Netconns.Netconn_Id;
   use type AIP_Netbufs.Netbuf_Id;
   use type AIP_Ctypes.S8_T;

   procedure Run is

      LC, AC : AIP_Netconns.Netconn_Id;
      ER : AIP_Ctypes.Err_T;

      NB : AIP_Netbufs.Netbuf_Id;
      Data : System.Address;
      Len : AIP_Ctypes.U16_T;
   begin
      LC := AIP_Netconns.Netconn_New (AIP_Netconns.NETCONN_TCP);

      ER := AIP_Netconns.Netconn_Bind (LC, AIP_IPaddrs.IP_ADDR_ANY, 7);
      AIP_Netconns.Netconn_Listen (LC);

      while True loop

         AC := AIP_Netconns.Netconn_Accept (LC);

         if AC /= AIP_Netconns.NOCONN then

            loop
               NB := AIP_Netconns.Netconn_Recv (AC);
               exit when NB = AIP_Netbufs.NOBUF;

               loop
                  AIP_Netbufs.Netbuf_Data (NB, Data, Len);
                  ER := AIP_Netconns.Netconn_Write
                    (AC, Data, Len, AIP_Netconns.NETCONN_COPY);
                  exit when AIP_Netbufs.Netbuf_Next (NB) < 0;
               end loop;

               AIP_Netbufs.Netbuf_Delete (NB);
            end loop;

            AIP_Netconns.Netconn_Close (AC);
            AIP_Netconns.Netconn_Delete (AC);
         end if;

      end loop;
   end Run;

end AIP_Tcpecho;
