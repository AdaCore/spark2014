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

   --------------------
   -- Available_Port --
   --------------------

   function Available_Port
     (PCB_Heads  : PCB_List;
      PCB_Pool   : IP_PCB_Array;
      Privileged : Boolean) return Port_T
   is
      Candidate : Port_T;
      Last      : Port_T;
      Pid       : PCB_Id;
   begin
      if Privileged then
         Candidate := 1023;
         Last      := 1;
      else
         Candidate := Config.First_Ephemeral_Port;
         Last      := Config.Last_Ephemeral_Port;
      end if;

      Scan_Ports : loop
         Find_PCB (Local_IP    => IPaddrs.IP_ADDR_ANY,
                   Local_Port  => Candidate,
                   Remote_IP   => IPaddrs.IP_ADDR_ANY,
                   Remote_Port => NOPORT,
                   PCB_Heads   => PCB_Heads,
                   PCB_Pool    => PCB_Pool,
                   PCB         => Pid);
         exit Scan_Ports when Pid = NOPCB;

         if Candidate = Last then
            Candidate := NOPORT;
            exit Scan_Ports;
         end if;

         if Privileged then
            Candidate := Candidate - 1;
         else
            Candidate := Candidate + 1;
         end if;
      end loop Scan_Ports;

      return Candidate;
   end Available_Port;

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
      PCB_Heads   : PCB_List;
      PCB_Pool    : IP_PCB_Array;
      PCB         : out PCB_Id)
   is
   begin
      for J in PCB_Heads'Range loop
         Find_PCB_In_List
           (Local_IP,
            Local_Port,
            Remote_IP,
            Remote_Port,
            PCB_Heads (J),
            PCB_Pool,
            PCB);
         exit when PCB /= NOPCB;
      end loop;
   end Find_PCB;

   ----------------------
   -- Find_PCB_In_List --
   ----------------------

   procedure Find_PCB_In_List
     (Local_IP    : IPaddrs.IPaddr;
      Local_Port  : Port_T;
      Remote_IP   : IPaddrs.IPaddr;
      Remote_Port : Port_T;
      PCB_Head    : PCB_Id;
      PCB_Pool    : IP_PCB_Array;
      PCB         : out PCB_Id)
   is
      Cid : PCB_Id;
      Ideal_PCB, Good_PCB : AIP.EID := NOPCB;

      Local_Match, Remote_Match : Boolean;

   begin
      --  Scan the given PCB list, looking for a PCB associated with the given
      --  local, and possibly remote, endpoint identifications.

      Cid := PCB_Head;

      loop
         exit when Ideal_PCB /= NOPCB or else Cid = NOPCB;

         --  See if the current PCB corresponds to the given local address. It
         --  does when the port numbers are the same and either the packet was
         --  broadcasted to the interface or the specific destination IP
         --  matches what PCB is listening to (when the latter is that IP or
         --  ANY). Note: IPaddrs.Match returns True if both addresses are the
         --  same or if either is ANY.

         Local_Match :=
           Match (PCB_Pool (Cid).Local_Port, Local_Port)
             and then
           (IPaddrs.Match (PCB_Pool (Cid).Local_IP, Local_IP)
              or else
            IPaddrs.Match (NIF.NIF_Broadcast (PCB_Pool (Cid).Netif),
                           Local_IP)
              or else
            IPaddrs.Match (IPaddrs.IP_ADDR_BCAST, Local_IP));

         --  If we don't have a local match, proceed with the next
         --  candidate. If we do have a local match, see if the PCB remote
         --  addr+port pair matches the transport source. If it does, the PCB
         --  is connected to that source and is an ideal taker. Otherwise,
         --  remember that PCB as a fallback possible destination if it is
         --  unconnected.

         if Local_Match then
            Remote_Match :=
              Match (PCB_Pool (Cid).Remote_Port, Remote_Port)
                and then
              IPaddrs.Match (PCB_Pool (Cid).Remote_IP, Remote_IP);

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
   end Find_PCB_In_List;

   -----------
   -- Match --
   -----------

   function Match (P1, P2 : Port_T) return Boolean is
   begin
      return P1 = NOPORT or else P2 = NOPORT or else P1 = P2;
   end Match;

end AIP.PCBs;
