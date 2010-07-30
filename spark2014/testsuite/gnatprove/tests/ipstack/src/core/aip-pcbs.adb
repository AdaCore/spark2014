------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.PCBs is

   ------------------
   -- Allocate_PCB --
   ------------------

   procedure Allocate_PCB
     (PCB_Pool : in out IP_PCB_Array;
      Id       : out AIP.EID)
   is
   begin
      --  Scan the PCBs array and pick the first unused entry

      Id := NOPCB;
      Scan_PCBs : for J in PCB_Pool'Range loop
         if PCB_Pool (J).Link = PCB_Unused then
            Id := J;
            PCB_Pool (J).Link := NOPCB;
            exit Scan_PCBs;
         end if;
      end loop Scan_PCBs;
   end Allocate_PCB;

   --------------
   -- Bound_To --
   --------------

   function Bound_To
     (PCB        : IP_PCB;
      Local_IP   : IPaddrs.IPaddr;
      Local_Port : Port_T) return Boolean
   is
   begin
      return PCB.Local_IP = Local_IP
        and then PCB.Local_Port = Local_Port;
      --  Case of PCB bound to IPaddrs.IP_ADDR_ANY ???
   end Bound_To;

   --------------
   -- Find_PCB --
   --------------

   procedure Find_PCB
     (Local_IP    : IPaddrs.IPaddr;
      Local_Port  : Port_T;
      Remote_IP   : IPaddrs.IPaddr;
      Remote_Port : Port_T;
      PCB_List    : AIP.EID;
      PCB_Pool    : IP_PCB_Array;
      PCB         : out PCB_Id)
   is
      Cid : AIP.EID;
      Ideal_PCB, Good_PCB : AIP.EID := NOPCB;

      Local_Match, Remote_Match : Boolean;

   begin
      --  Scan the list of bound PCBs in search of one at least locally bound
      --  to the datagram destination endpoint, and even better also connected
      --  to the remote source.

      Cid := PCB_List;

      loop
         exit when Ideal_PCB /= NOPCB or else Cid = NOPCB;

         --  See if PCB local addr+port match UDP destination addr+port

         Local_Match :=
           PCB_Pool (Cid).Local_Port = Local_Port
           and then
           (IPaddrs.Match (PCB_Pool (Cid).Local_IP, Local_IP)
              or else
            IPaddrs.Match (NIF.NIF_Broadcast (PCB_Pool (Cid).Netif),
                           Local_IP));
         --  ??? case of a datagram for the broadcast address arriving on
         --  one interface, and destined to the broadcast address of another,
         --  when we are bound on the specific address of the other interface?

         --  If it does, see if the PCB remote addr+port pair matches the
         --  UDP source, in which case we have an ideal taker. Otherwise,
         --  remember that PCB as a fallback possible destination if it is
         --  unconnected.

         if Local_Match then
            Remote_Match :=
              PCB_Pool (Cid).Remote_Port = Remote_Port
                 and then IPaddrs.Match (PCB_Pool (Cid).Remote_IP, Remote_IP);

            if Remote_Match then
               Ideal_PCB := Cid;

            elsif Good_PCB = NOPCB and then not PCB_Pool (Cid).Connected then
               Good_PCB := Cid;
            end if;
         end if;

         Cid := PCB_Pool (Cid).Link;
      end loop;

      if Ideal_PCB /= NOPCB then
         PCB := Ideal_PCB;
      else
         PCB := Good_PCB;
         --  Might be NULID
      end if;
   end Find_PCB;

end AIP.PCBs;
