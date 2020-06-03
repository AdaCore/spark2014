------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with AIP.ARPH;
with AIP.Conversions;
with AIP.EtherH;
with AIP.Inet;
with AIP.Timers;

package body AIP.ARP with
  Refined_State => (State => (ARP_Table, ARP_Free_List, ARP_Active_List))
is
   type ARP_Table_T is array (ARP_Entry_Id) of ARP_Entry;
   ARP_Table : ARP_Table_T;
   ARP_Free_List   : Any_ARP_Entry_Id;
   ARP_Active_List : Any_ARP_Entry_Id;

   ---------------------
   -- Get_MAC_Address --
   ---------------------

   function Get_MAC_Address (Nid : NIF.Netif_Id) return AIP.Ethernet_Address is
      Nid_LL_Address        : AIP.Ethernet_Address;
      Nid_LL_Address_Length : AIP.LL_Address_Range;
      pragma Warnings (Off, "unused assignment to ""Nid_LL_Address_Length""");
      --  Used in assertion only
   begin
      NIF.Get_LL_Address (Nid, Nid_LL_Address, Nid_LL_Address_Length);
      pragma Assert (Nid_LL_Address_Length = Nid_LL_Address'Last);
      return Nid_LL_Address;
   end Get_MAC_Address;

   -----------------
   -- Send_Packet --
   -----------------

   procedure Send_Packet
     (Nid             : NIF.Netif_Id;
      Frame_Type      : AIP.U16_T;
      Buf             : Buffers.Buffer_Id;
      Dst_MAC_Address : AIP.Ethernet_Address)
   is
      Err  : AIP.Err_T;
      Ehdr : System.Address;
   begin

      --  Prepend Ethernet header

      Buffers.Buffer_Header (Buf, EtherH.Ether_Header_Size / 8, Err);

      if AIP.No (Err) then
         Ehdr := Buffers.Buffer_Payload (Buf);
         EtherH.Set_EtherH_Dst_MAC_Address (Ehdr, Dst_MAC_Address);
         EtherH.Set_EtherH_Src_MAC_Address (Ehdr, Get_MAC_Address (Nid));
         EtherH.Set_EtherH_Frame_Type      (Ehdr, Frame_Type);

         pragma Warnings (Off, """Err"" is set by ""Link_Output"" but not used after the call");
         --  Ignore error from link output
         NIF.Link_Output (Nid, Buf, Err);
         pragma Warnings (On, """Err"" is set by ""Link_Output"" but not used after the call");
      end if;
   end Send_Packet;

   ------------------
   -- Send_Request --
   ------------------

   procedure Send_Request
     (Nid            : NIF.Netif_Id;
      Dst_IP_Address : IPaddrs.IPaddr)
   is
      Ethernet_Broadcast : constant AIP.Ethernet_Address :=
                             AIP.Ethernet_Address'(others => 16#ff#);

      Buf : Buffers.Buffer_Id;

      Ahdr : System.Address;
   begin
      Buffers.Buffer_Alloc
        (Offset => Inet.HLEN_To (Inet.LINK_LAYER),
         Size   => ARPH.ARP_Header_Size / 8,
         Kind   => Buffers.SPLIT_BUF,
         Buf    => Buf);

      if Buf /= Buffers.NOBUF then
         Ahdr := Buffers.Buffer_Payload (Buf);

         ARPH.Set_ARPH_Hardware_Type   (Ahdr, ARPH.ARP_Hw_Ethernet);
         ARPH.Set_ARPH_Protocol        (Ahdr, EtherH.Ether_Type_IP);
         ARPH.Set_ARPH_Hw_Len          (Ahdr, AIP.Ethernet_Address'Size / 8);
         ARPH.Set_ARPH_Pr_Len          (Ahdr, IPaddrs.IPaddr'Size / 8);
         ARPH.Set_ARPH_Operation       (Ahdr, ARPH.ARP_Op_Request);
         ARPH.Set_ARPH_Src_Eth_Address (Ahdr, Get_MAC_Address (Nid));
         ARPH.Set_ARPH_Src_IP_Address  (Ahdr, NIF.NIF_Addr (Nid));
         ARPH.Set_ARPH_Dst_Eth_Address (Ahdr, Ethernet_Broadcast);
         ARPH.Set_ARPH_Dst_IP_Address  (Ahdr, Dst_IP_Address);

         Send_Packet (Nid, EtherH.Ether_Type_ARP, Buf, Ethernet_Broadcast);
         Buffers.Buffer_Blind_Free (Buf);
      end if;
   end Send_Request;

   -----------------
   -- ARP_Prepend --
   -----------------

   procedure ARP_Prepend
     (List : in out Any_ARP_Entry_Id;
      AEID : ARP_Entry_Id)
   with
     Refined_Global => (In_Out => ARP_Table)
   is
   begin
      ARP_Table (AEID).Next := List;
      List := AEID;
   end ARP_Prepend;

   ----------------
   -- ARP_Unlink --
   ----------------

   procedure ARP_Unlink
     (List : in out Any_ARP_Entry_Id;
      AEID : ARP_Entry_Id)
   with
     Refined_Global => (In_Out => ARP_Table)
   is
      Prev, Cur : Any_ARP_Entry_Id;
   begin
      Prev := No_ARP_Entry;
      Cur  := List;
      while Cur /= AEID and then Cur /= No_ARP_Entry loop
         Prev := Cur;
         Cur := ARP_Table (Cur).Next;
      end loop;

      if Cur /= No_ARP_Entry then
         if Prev = No_ARP_Entry then
            List := ARP_Table (Cur).Next;
         else
            ARP_Table (Prev).Next := ARP_Table (Cur).Next;
         end if;
      end if;

      ARP_Table (AEID).Next := No_ARP_Entry;
   end ARP_Unlink;

   ---------------
   -- ARP_Reset --
   ---------------

   procedure ARP_Reset (AE : in out ARP_Entry) is
   begin
      AE.State        := Incomplete;
      AE.Permanent    := False;
      AE.Timestamp    := Time_Types.Time'First;
      AE.Packet_Queue := Buffers.Empty_Packet_Queue;
   end ARP_Reset;

   --------------
   -- ARP_Find --
   --------------

   procedure ARP_Find
     (Addr     : IPaddrs.IPaddr;
      Id       : out Any_ARP_Entry_Id;
      Allocate : Boolean)
   with
     Refined_Global => (In_Out => (ARP_Active_List, ARP_Free_List, ARP_Table))
   is
      Last_Active_Id : Any_ARP_Entry_Id;
   begin
      --  First look for address in active list

      Last_Active_Id := No_ARP_Entry;
      Id := ARP_Active_List;
      Scan_ARP_Entries : while Id /= No_ARP_Entry loop
         if ARP_Table (Id).Dst_IP_Address = Addr then

            --  Entry found

            ARP_Unlink (ARP_Active_List, Id);
            exit Scan_ARP_Entries;
         end if;

         --  Record entry as candidate for recycling, unless it is marked as
         --  permanent.

         if not ARP_Table (Id).Permanent then
            Last_Active_Id := Id;
         end if;

         Id := ARP_Table (Id).Next;
      end loop Scan_ARP_Entries;

      --  Entry not found, try to allocate a new one if requested

      if Id = No_ARP_Entry and then Allocate then
         if ARP_Free_List /= No_ARP_Entry then

            --  Allocate from free list if possible

            Id := ARP_Free_List;
            ARP_Unlink (ARP_Free_List, Id);

         elsif Last_Active_Id /= No_ARP_Entry then

            --  If free list is empty, recycle oldest active entry

            Id := Last_Active_Id;
            ARP_Unlink (ARP_Active_List, Id);
         end if;

         if Id /= No_ARP_Entry then

            --  Initialize newly-allocated entry

            ARP_Reset (ARP_Table (Id));
            ARP_Table (Id).Dst_IP_Address := Addr;
         end if;
      end if;

      --  If entry found or allocated, insert it at head of the active list

      if Id /= No_ARP_Entry then
         ARP_Prepend (ARP_Active_List, Id);
      end if;
   end ARP_Find;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize with
     Refined_Global => (Output => (ARP_Active_List, ARP_Free_List, ARP_Table))
   is
   begin
      ARP_Table := ARP_Table_T'
        (others => ARP_Entry'(State           => Unused,
                              Permanent       => False,
                              Timestamp       => 0,
                              Dst_IP_Address  => IPaddrs.IP_ADDR_ANY,
                              Dst_MAC_Address => AIP.Ethernet_Address'
                                                   (others => 0),
                              Packet_Queue    => Buffers.Empty_Packet_Queue,
                              Next            => No_ARP_Entry));
      for J in ARP_Entry_Id loop
         ARP_Table (J).Next := J - 1;
      end loop;
      ARP_Free_List := ARP_Table'Last;
      ARP_Active_List := No_ARP_Entry;

      Timers.Set_Interval (Timers.TIMER_EVT_ETHARPTMR, Time_Types.Hz);
   end Initialize;

   ----------------
   -- ARP_Update --
   ----------------

   procedure ARP_Update
     (Nid         : NIF.Netif_Id;
      Eth_Address : AIP.Ethernet_Address;
      IP_Address  : IPaddrs.IPaddr;
      Allocate    : Boolean;
      Err         : out AIP.Err_T)
   with
     Refined_Global =>
       (In_Out => (ARP_Active_List, ARP_Free_List, ARP_Table, Buffers.State))
   is
      AEID       : Any_ARP_Entry_Id;
      Packet_Buf : Buffers.Buffer_Id;
   begin
      Err := AIP.NOERR;

      ARP_Find (Addr => IP_Address, Id => AEID, Allocate => Allocate);
      if AEID = No_ARP_Entry then
         Err := AIP.ERR_MEM;
      end if;

      if AIP.No (Err) then
         ARP_Table (AEID).State := Active;
         ARP_Table (AEID).Timestamp := Time_Types.Now;
         ARP_Table (AEID).Dst_MAC_Address := Eth_Address;

         Flush_Queue : loop
            Buffers.Remove_Packet
              (Buffers.Link,
               ARP_Table (AEID).Packet_Queue,
               Packet_Buf);
            exit Flush_Queue when Packet_Buf = Buffers.NOBUF;

            Send_Packet (Nid, EtherH.Ether_Type_IP, Packet_Buf, Eth_Address);
            Buffers.Buffer_Blind_Free (Packet_Buf);
         end loop Flush_Queue;
      end if;
   end ARP_Update;

   ---------------
   -- ARP_Input --
   ---------------

   procedure ARP_Input
     (Nid                : NIF.Netif_Id;
      Netif_MAC_Addr_Ptr : System.Address;
      Buf                : Buffers.Buffer_Id)
   with
     Refined_Global =>
       (In_Out => (ARP_Active_List, ARP_Free_List, ARP_Table, Buffers.State))
   is
      Err        : AIP.Err_T;
      Ehdr, Ahdr : System.Address;
      Ifa        : IPaddrs.IPaddr;
      Local      : Boolean;

      ---------------
      -- Netif_MAC --
      ---------------

      function Netif_MAC return AIP.Ethernet_Address with
        Global => null
      is
         Result : Ethernet_Address;
         for Result'Address use Netif_MAC_Addr_Ptr;
         pragma Import (Ada, Result);
      begin
         return Result;
         pragma Annotate (GNATprove, Intentional,
                          """Result"" is not initialized",
                          "Result is initialized outside the program");
      end Netif_MAC;

   --  Start of processing for ARP_Input;

   begin
      Err := AIP.NOERR;
      Ifa := NIF.NIF_Addr (Nid);

      Ehdr := Buffers.Buffer_Payload (Buf);
      Ahdr := Conversions.Ofs (Ehdr, EtherH.Ether_Header_Size / 8);

      if Buffers.Buffer_Len (Buf) < (EtherH.Ether_Header_Size
                                       + ARPH.ARP_Header_Size) / 8
           or else
         ARPH.ARPH_Hardware_Type (Ahdr) /= ARPH.ARP_Hw_Ethernet
           or else
         ARPH.ARPH_Protocol (Ahdr) /= EtherH.Ether_Type_IP
           or else
         ARPH.ARPH_Hw_Len (Ahdr) /= AIP.Ethernet_Address'Size / 8
           or else
         ARPH.ARPH_Pr_Len (Ahdr) /= IPaddrs.IPaddr'Size / 8
      then
         --  Discard packet if short, or if not a consistent Ethernet/IP ARP
         --  message.

         Err := AIP.ERR_USE;
      end if;

      if AIP.No (Err) then
         Local := Ifa /= IPaddrs.IP_ADDR_ANY
                    and then Ifa = ARPH.ARPH_Dst_Ip_Address (Ahdr);

         --  Update entry for sender. If message is to us, assume we'll need to
         --  talk back to them, and allocate a new entry if none exists.

         ARP_Update
           (Nid         => Nid,
            Eth_Address => ARPH.ARPH_Src_Eth_Address (Ahdr),
            IP_Address  => ARPH.ARPH_Src_IP_Address (Ahdr),
            Allocate    => Local,
            Err         => Err);

         if AIP.No (Err) then
            case ARPH.ARPH_Operation (Ahdr) is
               when ARPH.ARP_Op_Request =>
                  if Local then
                     --  Send ARP reply, reusing original buffer

                     EtherH.Set_EtherH_Dst_MAC_Address (Ehdr,
                       EtherH.EtherH_Src_MAC_Address (Ehdr));
                     EtherH.Set_EtherH_Src_MAC_Address (Ehdr, Netif_MAC);

                     ARPH.Set_ARPH_Operation (Ahdr, ARPH.ARP_Op_Reply);

                     ARPH.Set_ARPH_Dst_Eth_Address (Ahdr,
                       ARPH.ARPH_Src_Eth_Address (Ahdr));
                     ARPH.Set_ARPH_Dst_IP_Address (Ahdr,
                       ARPH.ARPH_Src_IP_Address  (Ahdr));

                     ARPH.Set_ARPH_Src_Eth_Address (Ahdr, Netif_MAC);
                     ARPH.Set_ARPH_Src_IP_Address  (Ahdr, Ifa);

                     pragma Warnings (Off, """Err"" is set by ""Link_Output"" but not used after the call");
                     --  Ignore error from link output
                     NIF.Link_Output (Nid, Buf, Err);
                     pragma Warnings (On, """Err"" is set by ""Link_Output"" but not used after the call");
                  end if;

               when ARPH.ARP_Op_Reply =>
                  --  We updated the cache already, nothing more to do

                  null;

               when others =>
                  --  Invalid ARP operation, discard

                  null;
            end case;
         end if;
      end if;

      --  Free received packet

      Buffers.Buffer_Blind_Free (Buf);
   end ARP_Input;

   ----------------
   -- ARP_Output --
   ----------------

   procedure ARP_Output
     (Nid         : NIF.Netif_Id;
      Buf         : Buffers.Buffer_Id;
      Dst_Address : IPaddrs.IPaddr)
   with
     Refined_Global =>
       (In_Out => (ARP_Active_List, ARP_Free_List, ARP_Table, Buffers.State))
   is
      AEID : Any_ARP_Entry_Id;
   begin
      ARP_Find (Addr => Dst_Address, Id => AEID, Allocate => True);
      if AEID /= No_ARP_Entry then
         case ARP_Table (AEID).State is
            when Unused     =>
               --  Cannot happen

               null; --  raise Program_Error; ???

            when Active     =>
               Send_Packet
                 (Nid,
                  EtherH.Ether_Type_IP,
                  Buf,
                  ARP_Table (AEID).Dst_MAC_Address);

            when Incomplete =>

               --  Park packet on entry's pending list. Record this as an
               --  additional reference to Buf, which will be freed when the
               --  packet is removed from the queue.

               Buffers.Buffer_Ref (Buf);
               Buffers.Append_Packet
                 (Buffers.Link,
                  ARP_Table (AEID).Packet_Queue,
                  Buf);

               --  If last attempt is old enough (also case of a newly
               --  created incomplete entry), send out ARP request.
               --  Should we do that always, or conditionalize???

               Send_Request (Nid, Dst_Address);
         end case;
      else
         --  Unable to find or allocate ARP entry, discard packet

         null;
      end if;
   end ARP_Output;

   --  procedure ARP_Flush (All : Boolean)
   --  Common subprogram for ARP_Timer and ARP_Clear: remove all non-permanent
   --  entries (if All_Entries is True) or only obsolete ones (if it is False).

   ---------------
   -- ARP_Flush --
   ---------------

   procedure ARP_Flush (All_Entries : Boolean) with
     Global => (In_Out => (ARP_Active_List,
                           ARP_Free_List,
                           ARP_Table,
                           Buffers.State))
   is
      Now        : Time_Types.Time;
      AEID       : Any_ARP_Entry_Id;
      Next_AEID  : Any_ARP_Entry_Id;
      AE_Age     : Time_Types.Interval;
      Packet_Buf : Buffers.Buffer_Id;

   begin
      Now  := Time_Types.Now;
      AEID := ARP_Active_List;

      while AEID /= No_ARP_Entry loop
         Next_AEID := ARP_Table (AEID).Next;
         AE_Age := Now - ARP_Table (AEID).Timestamp;

         if not ARP_Table (AEID).Permanent
                 and then
               (All_Entries
                  or else
                (ARP_Table (AEID).State = Active
                   and then AE_Age > Max_ARP_Age_Active * Time_Types.Hz
                   and then Buffers.Empty (ARP_Table (AEID).Packet_Queue))
                  or else
                (ARP_Table (AEID).State = Incomplete
                   and then AE_Age > Max_ARP_Age_Incomplete * Time_Types.Hz))
         then
            loop
               Buffers.Remove_Packet
                 (Buffers.Link,
                  ARP_Table (AEID).Packet_Queue,
                  Packet_Buf);
               exit when Packet_Buf = Buffers.NOBUF;
               Buffers.Buffer_Blind_Free (Packet_Buf);
            end loop;
            ARP_Unlink (ARP_Active_List, AEID);
            ARP_Prepend (ARP_Free_List, AEID);
         end if;

         AEID := Next_AEID;
      end loop;
   end ARP_Flush;

   ---------------
   -- ARP_Timer --
   ---------------

   procedure ARP_Timer with
     Refined_Global =>
       (In_Out => (ARP_Active_List, ARP_Free_List, ARP_Table, Buffers.State))
   is
   begin
      ARP_Flush (All_Entries => False);
   end ARP_Timer;

   ---------------
   -- ARP_Clear --
   ---------------

   procedure ARP_Clear with
     Refined_Global =>
       (In_Out => (ARP_Active_List, ARP_Free_List, ARP_Table, Buffers.State))
   is
   begin
      ARP_Flush (All_Entries => True);
   end ARP_Clear;

   --------------
   -- IP_Input --
   --------------

   procedure IP_Input
     (Nid   : NIF.Netif_Id;
      Buf   : Buffers.Buffer_Id)
   with
     SPARK_Mode => Off
   is
      pragma Unreferenced (Nid, Buf);
   begin
      --  TBD???
      null;
   end IP_Input;

end AIP.ARP;
