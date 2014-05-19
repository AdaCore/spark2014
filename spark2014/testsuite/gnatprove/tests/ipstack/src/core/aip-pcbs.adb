------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

package body AIP.PCBs is

   --------------
   -- Allocate --
   --------------

   procedure Allocate
     (PCB_Pool : in out IP_PCB_Array;
      PCB      : out PCB_Id)
   is
   begin
      --  Scan the PCBs array and pick the first unused entry

      PCB := NOPCB;
      Scan_PCBs : for J in PCB_Pool'Range loop
         if PCB_Pool (J).Link = PCB_Unused then
            PCB := J;
            PCB_Pool (J) := IP_PCB_Initializer;
            PCB_Pool (J).Link := NOPCB;
            exit Scan_PCBs;
         end if;
      end loop Scan_PCBs;
   end Allocate;

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
   -- Bind_PCB --
   --------------

   procedure Bind_PCB
     (PCB        : PCB_Id;
      Local_IP   : IPaddrs.IPaddr;
      Local_Port : Port_T;
      PCB_Heads  : PCB_List;
      PCB_Pool   : in out IP_PCB_Array;
      Err        : out Err_T)
   is
      B_Port : Port_T := NOPORT;
      Other_PCB : PCB_Id;
   begin
      pragma Assert (PCB /= PCBs.NOPCB);
      Err := NOERR;

      if PCB_Pool (PCB).Local_Port /= NOPORT then
         Err := ERR_USE;

      elsif Local_Port = NOPORT then
         B_Port :=
           PCBs.Available_Port
             (PCB_Heads  => PCB_Heads,
              PCB_Pool   => PCB_Pool,
              Privileged => False);

         if B_Port = NOPORT then
            Err := ERR_MEM;
         end if;

      else
         B_Port := Local_Port;

         PCBs.Find_PCB (Local_IP    => Local_IP,
                        Local_Port  => B_Port,
                        Remote_IP   => IPaddrs.IP_ADDR_ANY,
                        Remote_Port => NOPORT,
                        PCB_Heads   => PCB_Heads,
                        PCB_Pool    => PCB_Pool,
                        PCB         => Other_PCB);

         if Other_PCB /= PCBs.NOPCB then
            Err := ERR_USE;
         end if;
      end if;

      if No (Err) then
         pragma Assert (B_Port /= NOPORT);

         PCB_Pool (PCB).Local_IP   := Local_IP;
         PCB_Pool (PCB).Local_Port := B_Port;
      end if;
   end Bind_PCB;

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
      Try_PCB      : PCB_Id;
      Try_Wildcard : Natural;
      Wildcard     : Natural := 3;
   begin
      PCB := NOPCB;
      for J in PCB_Heads'Range loop
         Find_PCB_In_List
           (Local_IP,
            Local_Port,
            Remote_IP,
            Remote_Port,
            PCB_Heads (J),
            PCB_Pool,
            Try_PCB,
            Try_Wildcard);

         if Try_Wildcard < Wildcard then
            PCB      := Try_PCB;
            Wildcard := Try_Wildcard;
         end if;
         exit when Wildcard = 0;
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
      PCB         : out PCB_Id;
      Wildcard    : out Natural)
   is
      Cid : PCB_Id;
      Match_Wildcard : Natural;

      function Wildcard_Count
        (Addr : IPaddrs.IPaddr;
         Port : Port_T) return Natural;
      --  Return 1 if Addr is IP_ADDR_ANY or Port is Any_Port, 0 otherwise

      --------------------
      -- Wildcard_Count --
      --------------------

      function Wildcard_Count
        (Addr : IPaddrs.IPaddr;
         Port : Port_T) return Natural
      is
         Count : Natural;
      begin
         if Addr = IPaddrs.IP_ADDR_ANY or else Port = NOPORT then
            Count := 1;
         else
            Count := 0;
         end if;
         return Count;
      end Wildcard_Count;

   --  Start of processing for Find_PCB_In_List

   begin
      PCB      := NOPCB;
      Wildcard := 3;

      --  Scan the given PCB list, looking for a PCB associated with the given
      --  local, and possibly remote, endpoint identifications.

      Cid := PCB_Head;

      while Cid /= NOPCB and then Wildcard > 0 loop
         --  See if the current PCB corresponds to the given local address. It
         --  does when the port numbers are the same and either the packet was
         --  broadcasted to the interface or the specific destination IP
         --  matches what PCB is listening to (when the latter is that IP or
         --  ANY). Note: IPaddrs.Match returns True if both addresses are the
         --  same or if either is ANY.

         if Match (PCB_Pool (Cid).Local_Port, Local_Port)
              and then
            (IPaddrs.Match (PCB_Pool (Cid).Local_IP, Local_IP)
               or else
             IPaddrs.Match (NIF.NIF_Broadcast (PCB_Pool (Cid).Netif),
                            Local_IP)
               or else
             IPaddrs.Match (IPaddrs.IP_ADDR_BCAST, Local_IP))

           and then
             Match (PCB_Pool (Cid).Remote_Port, Remote_Port)
               and then
             IPaddrs.Match (PCB_Pool (Cid).Remote_IP, Remote_IP)
         then
            Match_Wildcard :=
              Wildcard_Count
                (PCB_Pool (Cid).Local_IP, PCB_Pool (Cid).Local_Port)
              +
              Wildcard_Count
                (PCB_Pool (Cid).Remote_IP, PCB_Pool (Cid).Remote_Port);

            if Match_Wildcard < Wildcard then
               Wildcard := Match_Wildcard;
               PCB      := Cid;
            end if;
         end if;

         Cid := PCB_Pool (Cid).Link;
      end loop;
   end Find_PCB_In_List;

   -----------
   -- Match --
   -----------

   function Match (P1, P2 : Port_T) return Boolean is
   begin
      return P1 = NOPORT or else P2 = NOPORT or else P1 = P2;
   end Match;

   -------------
   -- Prepend --
   -------------

   procedure Prepend
     (PCB      : PCB_Id;
      PCB_Head : in out PCB_Id;
      PCB_Pool : in out IP_PCB_Array)
   is
   begin
      PCB_Pool (PCB).Link := PCB_Head;
      PCB_Head := PCB;
   end Prepend;

   ------------
   -- Unlink --
   ------------

   procedure Unlink
     (PCB : PCB_Id;
      PCB_Head : in out PCB_Id;
      PCB_Pool : in out IP_PCB_Array)
   is
      Cur, Prev : AIP.EID;
   begin
      pragma Assert (PCB /= NOPCB);

      if PCB = PCB_Head then
         PCB_Head := PCB_Pool (PCB).Link;

      else
         Prev := NOPCB;
         Cur  := PCB_Head;

         while Cur /= NOPCB and then PCB /= Cur loop
            Prev := Cur;
            Cur  := PCB_Pool (Cur).Link;
         end loop;

         if Cur /= PCBs.NOPCB then
            pragma Assert (Prev /= PCBs.NOPCB);
            PCB_Pool (Prev).Link := PCB_Pool (Cur).Link;
            PCB_Pool (Cur).Link  := NOPCB;
         end if;
      end if;
      PCB_Pool (PCB).Link := NOPCB;
   end Unlink;

end AIP.PCBs;
