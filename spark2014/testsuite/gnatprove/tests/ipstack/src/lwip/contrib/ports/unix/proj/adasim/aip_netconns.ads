------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System, AIP_Ctypes, AIP_IPaddrs, AIP_Netbufs;
--  # inherit System, AIP_Ctypes, AIP_IPaddrs, AIP_Netbufs;

package AIP_Netconns is

   type Netconn_Kind is
     (NETCONN_INVALID, NETCONN_TCP, NETCONN_UDP, NETCONN_RAW);
   for Netconn_Kind use
     (NETCONN_INVALID => 0,
      NETCONN_TCP => 16#10#,
      NETCONN_UDP => 16#20#,
      NETCONN_RAW => 16#40#);
   pragma Convention (C, Netconn_Kind);

   type Netconn_Id is private;
   NOCONN : constant Netconn_Id;

   subtype Callback is Integer;

   function Netconn_New (Ctype : Netconn_Kind) return Netconn_Id;

   function Netconn_Bind
     (NC : Netconn_Id;
      Addr : AIP_IPaddrs.IPaddr_Id;
      Port : AIP_Ctypes.U16_T)
     return AIP_Ctypes.Err_T;

   function Netconn_Recv
     (NC : Netconn_Id) return AIP_Netbufs.Netbuf_Id;

   function Netconn_Connect
     (NC : Netconn_Id;
      Addr : AIP_IPaddrs.IPaddr_Id;
      Port : AIP_Ctypes.U16_T)
     return AIP_Ctypes.Err_T;

   function Netconn_Send
     (NC : Netconn_Id;
      NB : AIP_Netbufs.Netbuf_Id)
     return AIP_Ctypes.Err_T;

   function Netconn_Accept
     (LC : Netconn_Id) return Netconn_Id;

   procedure Netconn_Listen_BL (NC : Netconn_Id; Backlog : AIP_Ctypes.U8_T);
   procedure Netconn_Listen (NC : Netconn_Id);

   procedure Netconn_Close (NC : Netconn_Id);
   procedure Netconn_Delete (NC : Netconn_Id);

   NETCONN_NOFLAGS : constant := 16#00#;
   NETCONN_COPY : constant := 16#01#;
   NETCONN_MORE : constant := 16#02#;

   function Netconn_Write
     (NC : Netconn_Id;
      Data  : System.Address;
      Len   : AIP_Ctypes.U16_T;
      Flags : AIP_Ctypes.U8_T)
     return AIP_Ctypes.Err_T;

private

   type Netconn is null record;
   type Netconn_Id is access all Netconn;

   NOCONN : constant Netconn_Id := null;

   function Netconn_New_PC
     (Ctype : Netconn_Kind;
      Proto : AIP_Ctypes.U8_T;
      Cb : Callback)
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

end AIP_Netconns;
