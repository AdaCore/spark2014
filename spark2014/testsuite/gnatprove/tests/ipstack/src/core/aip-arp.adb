------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.ARP is

   ARP_Table : array (ARP_Entry_Id) of ARP_Entry;
   ARP_Free_List   : Any_ARP_Entry_Id;
   ARP_Active_List : Any_ARP_Entry_Id;

   --------------
   -- ARP_Find --
   --------------

   procedure ARP_Find
     (Addr : IPaddrs.IPaddr;
      Id   : out Any_ARP_Entry_Id)
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

      --  Entry not found, try to allocate a new one

      if Id = No_ARP_Entry then
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

            declare
               New_Entry : ARP_Entry renames ARP_Table (Id);
            begin
               ARP_Reset (New_Entry);
               New_Entry.Dst_IP_Address := Addr;
            end;
         end if;
      end if;

      --  If entry found or allocated, mark it as active now and insert it at
      --  the head of the active list.

      if Id /= No_ARP_Entry then
         ARP_Prepend (ARP_Active_List, Id);
         ARP_Table (Id).Timestamp := Time_Types.Now;
      end if;
   end ARP_Find;

   --------------------
   -- ARP_Initialize --
   --------------------

   procedure ARP_Initialize is
   begin
      for J in ARP_Table'Range loop
         ARP_Table (J).State := Unused;
         ARP_Table (J).Next := J - 1;
      end loop;
      ARP_Free_List := ARP_Table'Last;
   end ARP_Initialize;

   ---------------
   -- ARP_Input --
   ---------------

   procedure ARP_Input
     (Nid           : NIF.Netif_Id;
      Netif_Address : IPTR_T;
      Buf           : Buffers.Buffer_Id)
   is
   begin
      --  TBD
      raise Program_Error;
   end ARP_Input;

   ----------------
   -- ARP_Output --
   ----------------

   procedure ARP_Output
     (Nid         : NIF.Netif_Id;
      Buf         : Buffers.Buffer_Id;
      Dst_Address : IPaddrs.IPaddr)
   is
      pragma Unreferenced (Nid, Buf);

      AEID : Any_ARP_Entry_Id;
   begin
      ARP_Find (Dst_Address, AEID);
      if AEID /= No_ARP_Entry then
         declare
            AE : ARP_Entry renames ARP_Table (AEID);
         begin
            case AE.State is
               when Unused     =>
                  --  Cannot happend
                  raise Program_Error;

               when Active     =>
                  --  Call netif low level output callback
                  --  TBD
                  raise Program_Error;

               when Incomplete =>
                  --  Park packet on entry pending list
                  --  TBD
                  raise Program_Error;
            end case;
         end;
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

   ---------------
   -- ARP_Reset --
   ---------------

   procedure ARP_Reset (AE : in out ARP_Entry) is
   begin
      AE.State     := Incomplete;
      AE.Permanent := False;
      AE.Timestamp := Time_Types.Time'First;
   end ARP_Reset;

   --------------
   -- IP_Input --
   --------------

   procedure IP_Input
     (Nid   : NIF.Netif_Id;
      Buf   : Buffers.Buffer_Id)
   is
   begin
      --  TBD
      raise Program_Error;
   end IP_Input;

end AIP.ARP;
