------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Protocol Control Blocks (shared between UDP and TCP)

with System;

with AIP.Config;
with AIP.IPaddrs;
with AIP.NIF;

package AIP.PCBs is

   subtype PCB_Id is AIP.EID
     range AIP.NULID .. AIP.EID'Max (Config.Max_UDP_PCB, Config.Max_TCP_PCB);
   PCB_Unused : constant AIP.EID := AIP.NULID - 1;
   --  Not in range of PCB_Id (see IP_PCB.Link below)

   NOPCB      : constant AIP.EID := AIP.NULID;
   --  In range of PCB_Id, denotes no valid PCB

   subtype Port_T is AIP.U16_T;
   NOPORT : constant Port_T := 0;

   function Match (P1, P2 : Port_T) return Boolean;
   --  True if P1 = P2 or either is NOPORT

   type IP_PCB is record
      Link        : AIP.EID;
      --  Link to next PCB. Set no PCB_Unused to mark unallocated PCBs, and to
      --  NOPCB for PCBs that are in use but not on a list (or last in list).

      Local_IP    : IPaddrs.IPaddr;
      Local_Port  : Port_T;

      Netif       : AIP.EID;
      --  If Local_IP is set to the IP address of a specific interface, Netif
      --  denotes that interface, else it is set to IF_NOID.

      Remote_IP   : IPaddrs.IPaddr;
      Remote_Port : Port_T;

      Connected   : Boolean;
      --  Set True when Remote_IP and Remote_Port are set.
      --  PCB.Connected is used to detect proper remote endpoint definition on
      --  UDP_Send, and to prevent selection of PCB to handle an incoming
      --  datagram if it is not connected to its remote origin (UDP_Input).

      SOO         : AIP.U16_T;
      --  Socket options
      --  Should use boolean components instead???

      TOS         : AIP.U8_T;
      --  Type Of Service

      TTL         : AIP.U8_T;
      --  Time To Live

      Udata       : System.Address;
      --  User/Application data pointer
   end record;

   IP_PCB_Initializer : constant IP_PCB :=
                          IP_PCB'(Link        => PCB_Unused,
                                  Local_IP    => IPaddrs.IP_ADDR_ANY,
                                  Local_Port  => 0,
                                  Netif       => NIF.IF_NOID,
                                  Remote_IP   => IPaddrs.IP_ADDR_ANY,
                                  Remote_Port => 0,
                                  Connected   => False,
                                  SOO         => 0,
                                  TOS         => 0,
                                  TTL         => 0,
                                  Udata       => System.Null_Address);

   subtype Valid_PCB_Id is PCB_Id range NOPCB + 1 .. PCB_Id'Last;
   type IP_PCB_Array is array (Valid_PCB_Id range <>) of IP_PCB;

   procedure Allocate
     (PCB_Pool : in out IP_PCB_Array;
      PCB      : out PCB_Id);
   --  Find an unused PCB in PCB_Pool (denoted by Link = PCB_Unused) and return
   --  its index, or NOPCB if none is found.

   --  In the subprograms below, PCB_Heads denote the heads of the various
   --  lists of in-use PCBs maintained by each higher level protocol (TCP or
   --  UDP), and PCB_Pool the array of IP_PCB objecs.

   type PCB_List is array (Natural range <>) of PCB_Id;

   procedure Bind_PCB
     (PCB        : PCB_Id;
      Local_IP   : IPaddrs.IPaddr;
      Local_Port : Port_T;
      PCB_Heads  : PCB_List;
      PCB_Pool   : in out IP_PCB_Array;
      Err        : out AIP.Err_T)
   --  Bind PCB to the given local address and port
   with
     Global => null;

   procedure Find_PCB
     (Local_IP    : IPaddrs.IPaddr;
      Local_Port  : Port_T;
      Remote_IP   : IPaddrs.IPaddr;
      Remote_Port : Port_T;
      PCB_Heads   : PCB_List;
      PCB_Pool    : IP_PCB_Array;
      PCB         : out PCB_Id)
   --  PCB_Heads denotes the heads of each PCB list to be considered
   --  PCB_Pool is the set of all PCBs, indexed by PCB Id.
   with
     Global => null;

   procedure Find_PCB_In_List
     (Local_IP    : IPaddrs.IPaddr;
      Local_Port  : Port_T;
      Remote_IP   : IPaddrs.IPaddr;
      Remote_Port : Port_T;
      PCB_Head    : PCB_Id;
      PCB_Pool    : IP_PCB_Array;
      PCB         : out PCB_Id;
      Wildcard    : out Natural)
   --  Same as above but search a single list whose head is PCB_Head. Wildcard
   --  counts how many items (0, 1 or 2) were a wildcard match.
   with
     Global => null;

   procedure Prepend
     (PCB      : PCB_Id;
      PCB_Head : in out PCB_Id;
      PCB_Pool : in out IP_PCB_Array);
   --  Prepend PCB to list whose head is PCB_Head

   procedure Unlink
     (PCB : PCB_Id;
      PCB_Head : in out PCB_Id;
      PCB_Pool : in out IP_PCB_Array);
   --  Remove PCB from list whose head is PCB_Head

private

   function Available_Port
     (PCB_Heads  : PCB_List;
      PCB_Pool   : IP_PCB_Array;
      Privileged : Boolean) return Port_T;
   --  Return a local port that is not in use for any of the lists whose heads
   --  are in PCB_Heads. If Privileged, try to find a port number < 1024.

   function Bound_To
     (PCB        : IP_PCB;
      Local_IP   : IPaddrs.IPaddr;
      Local_Port : Port_T) return Boolean;

end AIP.PCBs;
