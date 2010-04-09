------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Callbacks, AIP.IPaddrs, AIP.Netbufs;
--# inherit AIP.Config, AIP.Callbacks, AIP.IPaddrs, AIP.Netbufs;

package AIP.Netconns is

   type Netconn_Kind is
     (NETCONN_INVALID, NETCONN_TCP, NETCONN_UDP, NETCONN_RAW);
   for Netconn_Kind use
     (NETCONN_INVALID => 0,
      NETCONN_TCP => 16#10#,
      NETCONN_UDP => 16#20#,
      NETCONN_RAW => 16#40#);
   pragma Convention (C, Netconn_Kind);

   subtype Netconn_Id is AIP.IPTR_T;
   NOCONN : constant Netconn_Id := AIP.NULID;

   subtype Callback is Integer;

   function Netconn_New (Ctype : Netconn_Kind) return Netconn_Id;

   function Netconn_Bind
     (NC : Netconn_Id;
      Addr : AIP.IPaddrs.IPaddr_Id;
      Port : AIP.U16_T)
     return AIP.Err_T;

   function Netconn_Recv
     (NC : Netconn_Id) return AIP.Netbufs.Netbuf_Id;

   function Netconn_Connect
     (NC : Netconn_Id;
      Addr : AIP.IPaddrs.IPaddr_Id;
      Port : AIP.U16_T)
     return AIP.Err_T;

   function Netconn_Send
     (NC : Netconn_Id;
      NB : AIP.Netbufs.Netbuf_Id)
     return AIP.Err_T;

   function Netconn_Accept
     (LC : Netconn_Id) return Netconn_Id;

   procedure Netconn_Listen_BL (NC : Netconn_Id; Backlog : AIP.U8_T);
   procedure Netconn_Listen (NC : Netconn_Id);

   procedure Netconn_Close (NC : Netconn_Id);
   procedure Netconn_Delete (NC : Netconn_Id);

   NETCONN_NOFLAGS : constant := 16#00#;
   NETCONN_COPY : constant := 16#01#;
   NETCONN_MORE : constant := 16#02#;

   function Netconn_Write
     (NC : Netconn_Id;
      Data  : AIP.IPTR_T;
      Len   : AIP.U16_T;
      Flags : AIP.U8_T)
     return AIP.Err_T;

private

   --  At this point, we provide straight bindings to the LWIP
   --  implementation, with extra _w wrapper functions as needed.

   --# hide AIP.Netconns;

   function Netconn_New_PC
     (Ctype : Netconn_Kind;
      Proto : AIP.U8_T;
      Cb : AIP.IPTR_T)
     return Netconn_Id;

   pragma Import (C, Netconn_New_PC, "netconn_new_with_proto_and_callback");
   pragma Import (C, Netconn_Bind, "netconn_bind");
   pragma Import (C, Netconn_Recv, "netconn_recv");
   pragma Import (C, Netconn_Connect, "netconn_connect");
   pragma Import (C, Netconn_Send, "netconn_send");

   pragma Import (C, Netconn_Accept, "netconn_accept");
   pragma Import (C, Netconn_Listen_BL, "netconn_listen_with_backlog");

   pragma Import (C, Netconn_Close, "netconn_close");
   pragma Import (C, Netconn_Delete, "netconn_delete");
   pragma Import (C, Netconn_Write, "netconn_write");

end AIP.Netconns;
