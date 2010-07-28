------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.ARPH;
with AIP.Conversions;
with AIP.EtherH;
with AIP.Inet;

package body AIP.ARP is

   ARP_Table : array (ARP_Entry_Id) of ARP_Entry;
   ARP_Free_List   : Any_ARP_Entry_Id;
   ARP_Active_List : Any_ARP_Entry_Id;

   --------------
   -- ARP_Find --
   --------------

   procedure ARP_Find
     (Addr     : IPaddrs.IPaddr;
      Id       : out Any_ARP_Entry_Id;
      Allocate : Boolean)
   is
      Last_Active_Id : Any_ARP_Entry_Id;
   begin
      --  First look for address in active list

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

   procedure Initialize is
   begin
      for J in ARP_Table'Range loop
         ARP_Table (J).State := Unused;
         ARP_Table (J).Next := J - 1;
      end loop;
      ARP_Free_List := ARP_Table'Last;
   end Initialize;

   ---------------
   -- ARP_Input --
   ---------------

   procedure ARP_Input
     (Nid                : NIF.Netif_Id;
      Netif_MAC_Addr_Ptr : System.Address;
      Buf                : Buffers.Buffer_Id)
   is
      Err  : Err_T := NOERR;

      Ehdr : constant System.Address := Buffers.Buffer_Payload (Buf);
      Ahdr : constant System.Address :=
               Conversions.Ofs (Ehdr, EtherH.Ether_Header'Size / 8);

      Ifa : constant IPaddrs.IPaddr := NIF.NIF_Addr (Nid);

      Local : Boolean;

      Netif_MAC : Ethernet_Address;
      for Netif_MAC'Address use Netif_MAC_Addr_Ptr;
      pragma Import (Ada, Netif_MAC);

   begin
      if Buffers.Buffer_Len (Buf) < Ahdr'Size / 8
           or else
         ARPH.ARPH_Hardware_Type (Ahdr) /= ARPH.ARP_Hw_Ethernet
           or else
         ARPH.ARPH_Protocol (Ahdr) /= EtherH.Ether_Type_IP
           or else
         ARPH.ARPH_Hw_Len (Ahdr) /= Ethernet_Address'Size / 8
           or else
         ARPH.ARPH_Pr_Len (Ahdr) /= IPaddrs.IPaddr'Size / 8
      then
         --  Discard packet if short, or if not a consistent Ethernet/IP ARP
         --  message.

         Err := ERR_USE;
      end if;

      if No (ERR) then
         Local := Ifa /= IPaddrs.IP_ADDR_ANY
                    and then Ifa = ARPH.ARPH_Dst_Ip_Address (Ahdr);

         --  Update entry for sender. If message is to us, assume we'll need to
         --  talk back to them, and allocate a new entry if none exists.

         ARP_Update
           (Nid,
            ARPH.ARPH_Src_Eth_Address (Ahdr),
            ARPH.ARPH_Src_IP_Address (Ahdr),
            Allocate => Local,
            Err      => Err);
      end if;

      if No (Err) then
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

                  NIF.Link_Output (Nid, Buf, Err);
               end if;

            when ARPH.ARP_Op_Reply =>
               --  We updated the cache already, nothing more to do

               null;

            when others =>
               --  Invalid ARP operation, discard

               null;
         end case;
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
   is
      AEID : Any_ARP_Entry_Id;
   begin
      ARP_Find (Dst_Address, AEID, Allocate => True);
      if AEID /= No_ARP_Entry then
         case ARP_Table (AEID).State is
            when Unused     =>
               --  Cannot happen

               raise Program_Error;

            when Active     =>
               Send_Packet
                 (Nid,
                  EtherH.Ether_Type_IP,
                  Buf,
                  ARP_Table (AEID).Dst_MAC_Address);

            when Incomplete =>
               --  Park packet on entry's pending list

               Buffers.Append_Packet (ARP_Table (AEID).Packet_Queue, Buf);

               --  If last attempt is old enough (also case of a newly
               --  created incomplete entry), send out ARP request.
               --  Condition to be refined???

               if True then
                  Send_Request (Nid, Dst_Address);
               end if;
         end case;
      else
         --  Unable to find or allocate ARP entry, discard packet

         null;
      end if;
   end ARP_Output;

   -----------------
   -- ARP_Prepend --
   -----------------

   procedure ARP_Prepend
     (List : in out Any_ARP_Entry_Id;
      AEID : ARP_Entry_Id)
   is
      AE : ARP_Entry renames ARP_Table (AEID);
   begin
      pragma Assert (AE.Prev = No_ARP_Entry);
      AE.Next := List;
      if List /= No_ARP_Entry then
         ARP_Table (List).Prev := AEID;
      end if;
      List := AEID;
   end ARP_Prepend;

   ---------------
   -- ARP_Timer --
   ---------------

   procedure ARP_Timer is
      use type Time_Types.Time;
      Now : constant Time_Types.Time := Time_Types.Now;
      AEID : Any_ARP_Entry_Id := ARP_Active_List;
      Next_AEID : Any_ARP_Entry_Id;

      procedure Check_Entry (AEID : ARP_Entry_Id);
      --  Check one entry from the active list (which is Active or Incomplete)

      -----------------
      -- Check_Entry --
      -----------------

      procedure Check_Entry (AEID : ARP_Entry_Id) is
         AE         : ARP_Entry renames ARP_Table (AEID);
         AE_Age     : constant Time_Types.Interval := Now - AE.Timestamp;
         Packet_Buf : Buffers.Buffer_Id;
      begin
         if not AE.Permanent
                 and then
               ((AE.State = Active
                   and then AE_Age > Max_ARP_Age_Active * Time_Types.Hz
                   and then Buffers.Empty (AE.Packet_Queue))
                  or else
                (AE.State = Incomplete
                   and then AE_Age > Max_ARP_Age_Incomplete * Time_Types.Hz))
         then
            loop
               Buffers.Remove_Packet (AE.Packet_Queue, Packet_Buf);
               exit when Packet_Buf = Buffers.NOBUF;
               Buffers.Buffer_Blind_Free (Packet_Buf);
            end loop;
            ARP_Unlink (ARP_Active_List, AEID);
         end if;
      end Check_Entry;

   --  Start of processing for ARP_Timer

   begin
      while AEID /= No_ARP_Entry loop
         Next_AEID := ARP_Table (AEID).Next;
         Check_Entry (AEID);
         AEID := Next_AEID;
      end loop;
   end ARP_Timer;

   ----------------
   -- ARP_Unlink --
   ----------------

   procedure ARP_Unlink
     (List : in out Any_ARP_Entry_Id;
      AEID : ARP_Entry_Id)
   is
      AE : ARP_Entry renames ARP_Table (AEID);
   begin
      if List = AEID then
         List := AE.Next;
      else
         pragma Assert (AE.Prev /= No_ARP_Entry);
         ARP_Table (AE.Prev).Next := AE.Next;
      end if;

      AE.Prev := No_ARP_Entry;
      AE.Next := No_ARP_Entry;
   end ARP_Unlink;

   ----------------
   -- ARP_Update --
   ----------------

   procedure ARP_Update
     (Nid         : NIF.Netif_Id;
      Eth_Address : Ethernet_Address;
      IP_Address  : IPaddrs.IPaddr;
      Allocate    : Boolean;
      Err         : out Err_T)
   is
      AEID : Any_ARP_Entry_Id;

      Packet_Buf : Buffers.Buffer_Id;
   begin
      Err := NOERR;

      ARP_Find (IP_Address, AEID, Allocate => Allocate);
      if AEID = No_ARP_Entry then
         Err := ERR_MEM;
      end if;

      if No (Err) then
         ARP_Table (AEID).State := Active;
         ARP_Table (AEID).Timestamp := Time_Types.Now;
         ARP_Table (AEID).Dst_MAC_Address := Eth_Address;

         Flush_Queue : loop
            Buffers.Remove_Packet (ARP_Table (AEID).Packet_Queue, Packet_Buf);
            exit Flush_Queue when Packet_Buf = Buffers.NOBUF;

            Send_Packet
              (Nid, EtherH.Ether_Type_IP, Packet_Buf, Eth_Address);
         end loop Flush_Queue;
      end if;
   end ARP_Update;

   ---------------
   -- ARP_Reset --
   ---------------

   procedure ARP_Reset (AE : in out ARP_Entry) is
   begin
      AE.State        := Incomplete;
      AE.Permanent    := False;
      AE.Timestamp    := Time_Types.Time'First;
      AE.Packet_Queue := Buffers.Empty_Packet_List;
   end ARP_Reset;

   ---------------------
   -- Get_MAC_Address --
   ---------------------

   function Get_MAC_Address (Nid : NIF.Netif_Id) return Ethernet_Address is
      Nid_LL_Address        : Ethernet_Address;
      Nid_LL_Address_Length : LL_Address_Range;
   begin
      NIF.Get_LL_Address (Nid, Nid_LL_Address, Nid_LL_Address_Length);
      pragma Assert (Nid_LL_Address_Length = Nid_LL_Address'Last);
      return Nid_LL_Address;
   end Get_MAC_Address;

   --------------
   -- IP_Input --
   --------------

   procedure IP_Input
     (Nid   : NIF.Netif_Id;
      Buf   : Buffers.Buffer_Id)
   is
   begin
      --  TBD???
      null;
   end IP_Input;

   -----------------
   -- Send_Packet --
   -----------------

   procedure Send_Packet
     (Nid             : NIF.Netif_Id;
      Frame_Type      : U16_T;
      Buf             : Buffers.Buffer_Id;
      Dst_MAC_Address : Ethernet_Address)
   is
      Err  : Err_T;
      Ehdr : System.Address;
   begin

      --  Prepend Ethernet header

      Buffers.Buffer_Header (Buf, EtherH.Ether_Header'Size / 8, Err);

      if No (Err) then
         Ehdr := Buffers.Buffer_Payload (Buf);
         EtherH.Set_EtherH_Dst_MAC_Address (Ehdr, Dst_MAC_Address);
         EtherH.Set_EtherH_Src_MAC_Address (Ehdr, Get_MAC_Address (Nid));
         EtherH.Set_EtherH_Frame_Type      (Ehdr, Frame_Type);

         NIF.Link_Output (Nid, Buf, Err);
      end if;
   end Send_Packet;

   ------------------
   -- Send_Request --
   ------------------

   procedure Send_Request
     (Nid            : NIF.Netif_Id;
      Dst_IP_Address : IPaddrs.IPaddr)
   is
      Ethernet_Broadcast : constant Ethernet_Address := (others => 16#ff#);

      Buf : Buffers.Buffer_Id;

      Ahdr : System.Address;
   begin
      Buffers.Buffer_Alloc
        (Buffers.SPLIT_BUF,
         Inet.HLEN_To (Inet.LINK_LAYER),
         ARPH.ARP_Header'Size / 8,
         Buf);

      if Buf /= Buffers.NOBUF then
         Ahdr := Buffers.Buffer_Payload (Buf);

         ARPH.Set_ARPH_Hardware_Type   (Ahdr, ARPH.ARP_Hw_Ethernet);
         ARPH.Set_ARPH_Protocol        (Ahdr, EtherH.Ether_Type_IP);
         ARPH.Set_ARPH_Hw_Len          (Ahdr, Ethernet_Address'Size / 8);
         ARPH.Set_ARPH_Pr_Len          (Ahdr, IPaddrs.IPaddr'Size);
         ARPH.Set_ARPH_Operation       (Ahdr, ARPH.ARP_Op_Request);
         ARPH.Set_ARPH_Src_Eth_Address (Ahdr, Get_MAC_Address (Nid));
         ARPH.Set_ARPH_Src_IP_Address  (Ahdr, NIF.NIF_Addr (Nid));
         ARPH.Set_ARPH_Dst_Eth_Address (Ahdr, Ethernet_Broadcast);
         ARPH.Set_ARPH_Dst_IP_Address  (Ahdr, Dst_IP_Address);

         Send_Packet (Nid, EtherH.Ether_Type_ARP, Buf, Ethernet_Broadcast);
         Buffers.Buffer_Blind_Free (Buf);
      end if;
   end Send_Request;

end AIP.ARP;
