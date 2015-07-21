------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2015, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with AIP.Buffers.Common;
with AIP.Buffers.Data;
with AIP.Buffers.No_Data;
with AIP.Conversions;
with AIP.Support;

use type AIP.Buffers.Common.Packet_Queue_Ptrs;

package body AIP.Buffers with
  Refined_State => (State => (AIP.Buffers.Common.Buf_List,
                              AIP.Buffers.Data.State,
                              AIP.Buffers.Data.Free_List,
                              AIP.Buffers.No_Data.State,
                              AIP.Buffers.No_Data.Free_List))
is

   -------------------
   -- Append_Packet --
   -------------------

   procedure Append_Packet
     (Layer : Packet_Layer;
      Queue : in out Packet_Queue;
      Buf   : Buffer_Id)
   with
     Refined_Global => (In_Out => Common.Buf_List)
   is
   begin
      if Queue.Tail /= NOBUF then
         Common.Buf_List (Queue.Tail).Next_Packet (Layer) := Buf;
         Queue.Tail := Buf;
      else
         Queue.Head := Buf;
         Queue.Tail := Buf;
      end if;

      --  Buf may be followed by other packets, so advance Tail as needed

      while Common.Buf_List (Queue.Tail).Next_Packet (Layer) /= NOBUF loop
         Queue.Tail := Common.Buf_List (Queue.Tail).Next_Packet (Layer);
      end loop;
   end Append_Packet;

   -----------------
   -- Buffer_Copy --
   -----------------

   procedure Buffer_Copy
     (Dst : Buffer_Id;
      Src : Buffer_Id;
      Len : AIP.U16_T;
      Err : out AIP.Err_T)
   with
     Refined_Global => (In_Out => (Data.State, No_Data.State)),
     SPARK_Mode => Off  --  Modifications through aliasing
   is
      type Data_Ty is array (1 .. Len) of U8_T;

      Src_Data : Data_Ty;
      for Src_Data'Address use Buffer_Payload (Src);
      pragma Import (Ada, Src_Data);

      Dst_Data : Data_Ty;
      for Dst_Data'Address use Buffer_Payload (Dst);
      pragma Import (Ada, Dst_Data);

   begin
      if Buffer_Len (Dst) < Len or else Buffer_Len (Src) < Len then
         Err := ERR_MEM;
      else
         Dst_Data := Src_Data;
         Err := NOERR;
      end if;
   end Buffer_Copy;

   -----------------
   -- Buffer_Init --
   -----------------

   procedure Buffer_Init with
     Refined_Global => (Output => (Common.Buf_List,
                                   Data.Free_List,
                                   Data.State,
                                   No_Data.Free_List,
                                   No_Data.State))
   is
   begin
      --  Zero out all the memory for common buffers data structure to zero

      Common.Buf_List :=
        Common.Buffer_Array'
          (others =>
               Common.Buffer'(Next          => NOBUF,
                              Next_Packet   =>
                                Common.Packet_Queue_Ptrs'(others => NOBUF),
                              Packet_Info   => System.Null_Address,
                              Len           => 0,
                              Tot_Len       => 0,
                              Alloc_Len     => 0,
                              Alloc_Tot_Len => 0,
                              Poffset       => 0,
                              Ref           => 0));

      --  Construct two singly linked chains of common buffer structures, one
      --  for data buffers and another for no-data buffers. Then Initialize
      --  data/no-data specific structures.

      for Buf in Common.Buffer_Index range 1 .. Common.Buffer_Index'Last - 1
      loop
         --  Do not link together the free list of data buffers and the free
         --  list of no-data buffers.

         if Buf /= Config.Data_Buffer_Num then
            Common.Buf_List (Buf).Next := Buf + 1;
         end if;
      end loop;

      No_Data.Buffer_Init;
      Data.Buffer_Init;
   end Buffer_Init;

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Offset : Buffer_Length;
      Size   : Data_Length;
      Kind   : Data_Buffer_Kind;
      Buf    : out Buffer_Id)
   with
     Refined_Global => (In_Out => (Common.Buf_List,
                                   Data.Free_List,
                                   Data.State))
   is

      Dbuf : Data.Dbuf_Id;
   begin
      Data.Buffer_Alloc
        (Offset => Offset,
         Size   => Size,
         Kind   => Kind,
         Buf    => Dbuf);
      Buf := Data.To_Common_Id (Dbuf);
      pragma Assert (Common.Buf_List (Buf).Next_Packet =
                       Common.Packet_Queue_Ptrs'(others => NOBUF));
   end Buffer_Alloc;

   ----------------------
   -- Ref_Buffer_Alloc --
   ----------------------

   procedure Ref_Buffer_Alloc
     (Offset   : Buffer_Length;
      Size     : Data_Length;
      Data_Ref : System.Address;
      Buf      : out Buffer_Id)
   with
     Refined_Global => (In_Out => (Common.Buf_List,
                                   No_Data.Free_List,
                                   No_Data.State))
   is
      Rbuf : No_Data.Rbuf_Id;
   begin
      No_Data.Buffer_Alloc
        (Offset   => Offset,
         Size     => Size,
         Data_Ref => Data_Ref,
         Buf      => Rbuf);
      Buf := No_Data.To_Common_Id (Rbuf);
      pragma Assert (Common.Buf_List (Buf).Next_Packet =
                       Common.Packet_Queue_Ptrs'(others => NOBUF));
   end Ref_Buffer_Alloc;

   ---------------------
   -- Buffer_Get_Kind --
   ---------------------

   function Buffer_Get_Kind (Buf : Buffer_Id) return Buffer_Kind with
     Refined_Global => Data.State
   is
      Kind : Buffer_Kind;
   begin
      if Common.Is_Data_Buffer (Buf) then
         Kind := Data.Buffer_Get_Kind (Data.To_Dbuf_Id (Buf));
      else
         Kind := REF_BUF;
      end if;
      return Kind;
   end Buffer_Get_Kind;

   ----------------
   -- Buffer_Len --
   ----------------

   function Buffer_Len (Buf : Buffer_Id) return AIP.U16_T with
     Refined_Global => Common.Buf_List
   is
   begin
      return Common.Buf_List (Buf).Len;
   end Buffer_Len;

   -----------------
   -- Buffer_Tlen --
   -----------------

   function Buffer_Tlen (Buf : Buffer_Id) return AIP.U16_T with
     Refined_Global => Common.Buf_List
   is
   begin
      return Common.Buf_List (Buf).Tot_Len;
   end Buffer_Tlen;

   -----------------
   -- Buffer_Next --
   -----------------

   function Buffer_Next (Buf : Buffer_Id) return Buffer_Id with
     Refined_Global => Common.Buf_List
   is
   begin
      return Common.Buf_List (Buf).Next;
   end Buffer_Next;

   --------------------
   -- Buffer_Payload --
   --------------------

   function Buffer_Payload (Buf : Buffer_Id) return System.Address with
     Refined_Global => (Common.Buf_List, Data.State, No_Data.State)
   is
      Result : System.Address;
   begin
      if Common.Is_Data_Buffer (Buf) then
         Result := Data.Buffer_Payload (Data.To_Dbuf_Id (Buf));
      else
         Result := No_Data.Buffer_Payload (No_Data.To_Rbuf_Id (Buf));
      end if;
      return Result;
   end Buffer_Payload;

   --------------------
   -- Buffer_Poffset --
   --------------------

   function Buffer_Poffset (Buf : Buffer_Id) return AIP.U16_T with
     Refined_Global => Common.Buf_List
   is
   begin
      return Common.Buf_List (Buf).Poffset;
   end Buffer_Poffset;

   -------------------
   -- Buffer_Header --
   -------------------

   procedure Buffer_Header
     (Buf  : Buffer_Id;
      Bump : AIP.S16_T;
      Err  : out AIP.Err_T)
   with
     Refined_Global => (In_Out => Common.Buf_List)
   is
      Offset : AIP.U16_T;
   begin
      Offset := AIP.U16_T (abs (Bump));
      Err    := AIP.NOERR;

      --  Check that we are not going to move off the buffer data

      if Bump < 0 then

         --  Moving forward - not beyond end of buffer data

         Support.Verify_Or_Err
           (Offset <= Common.Buf_List (Buf).Len, Err, AIP.ERR_MEM);

      elsif Bump > 0 then

         --  Moving backward - no before start of buffer data

         Support.Verify_Or_Err
           (Offset <= Common.Buf_List (Buf).Poffset, Err, AIP.ERR_MEM);
      end if;

      --  Adjust payload offset and lengths if all went fine

      if Bump /= 0 and then AIP.No (Err) then

         if Bump > 0 then
            Common.Buf_List (Buf).Poffset :=
              Common.Buf_List (Buf).Poffset - Offset;

            Common.Buf_List (Buf).Len     :=
              Common.Buf_List (Buf).Len + Offset;
            Common.Buf_List (Buf).Tot_Len :=
              Common.Buf_List (Buf).Tot_Len + Offset;
         else
            Common.Buf_List (Buf).Poffset :=
              Common.Buf_List (Buf).Poffset + Offset;

            Common.Buf_List (Buf).Len :=
              Common.Buf_List (Buf).Len - Offset;
            Common.Buf_List (Buf).Tot_Len :=
              Common.Buf_List (Buf).Tot_Len - Offset;
         end if;
      end if;
   end Buffer_Header;

   ------------------------
   -- Buffer_Set_Payload --
   ------------------------

   procedure Buffer_Set_Payload
     (Buf   : Buffer_Id;
      Pload : System.Address;
      Err   : out AIP.Err_T)
   with
     Refined_Global => (Input  => (Data.State, No_Data.State),
                        In_Out => Common.Buf_List)
   is
      Pload_Shift : AIP.S16_T;
      --  Amount by which we need to shift the payload pointer. Positive
      --  for a move forward.
   begin
      Pload_Shift :=
        AIP.S16_T (Conversions.Diff (Pload, Buffer_Payload (Buf)));
      Buffer_Header (Buf, -Pload_Shift, Err);
   end Buffer_Set_Payload;

   ---------------------------
   -- Buffer_Set_Paylod_Len --
   ---------------------------

   procedure Buffer_Set_Payload_Len
     (Buf : Buffer_Id;
      Len : AIP.U16_T;
      Err : out AIP.Err_T)
   with
     Refined_Global => (Input  => Data.State,
                        In_Out => Common.Buf_List)
   is
      Kind    : Buffer_Kind;
      Cur_Buf : Buffer_Id;
      New_Len : AIP.U16_T;
   begin
      Kind    := Buffer_Get_Kind (Buf);
      New_Len := Len;

      if Len > Common.Buf_List (Buf).Alloc_Tot_Len then
         Err     := AIP.ERR_MEM;
         Cur_Buf := NOBUF;

      else
         Err     := AIP.NOERR;
         Cur_Buf := Buf;
      end if;

      while Cur_Buf /= NOBUF
              and then New_Len /= Common.Buf_List (Cur_Buf).Tot_Len
      loop
         Common.Buf_List (Cur_Buf).Tot_Len := New_Len;

         case Kind is
            when SPLIT_BUF =>
               Common.Buf_List (Cur_Buf).Len := New_Len;
               if New_Len > Config.Data_Buffer_Size then
                  New_Len := New_Len - Config.Data_Buffer_Size;
               else
                  New_Len := 0;
               end if;

            when REF_BUF =>
               Common.Buf_List (Cur_Buf).Len := New_Len;
               New_Len := 0;
               pragma Assert (Common.Buf_List (Cur_Buf).Next = NOBUF);

            when LINK_BUF =>
               Common.Buf_List (Cur_Buf).Len :=
                 AIP.U16_T'Min (Common.Buf_List (Cur_Buf).Alloc_Len,
                                New_Len);
               New_Len := New_Len - Common.Buf_List (Cur_Buf).Len;
         end case;

         Cur_Buf := Common.Buf_List (Cur_Buf).Next;
      end loop;
   end Buffer_Set_Payload_Len;

   ----------------
   -- Buffer_Ref --
   ----------------

   procedure Buffer_Ref (Buf : Buffer_Id) with
     Refined_Global => (In_Out => Common.Buf_List)
   is
   begin
      Common.Buf_List (Buf).Ref := Common.Buf_List (Buf).Ref + 1;
   end Buffer_Ref;

   -----------------
   -- Buffer_Free --
   -----------------

   procedure Buffer_Free (Buf : Buffer_Id; N_Deallocs : out AIP.U8_T) with
     Refined_Global => (In_Out => (Common.Buf_List,
                                   Data.Free_List,
                                   Data.State,
                                   No_Data.Free_List))
   is
      Cur_Buf, Next_Buf : Buffer_Id;

   begin
      Next_Buf   := Buf;
      N_Deallocs := 0;

      while Next_Buf /= NOBUF loop

         Cur_Buf := Next_Buf;

         --  Decrease reference count

         Common.Buf_List (Cur_Buf).Ref := Common.Buf_List (Cur_Buf).Ref - 1;

         --  If reference count reaches zero, deallocate buffer

         if Common.Buf_List (Cur_Buf).Ref = 0 then

            --  Cur_Buf should not be on a packet queue anymore

            pragma Assert (Common.Buf_List (Cur_Buf).Next_Packet =
                             Common.Packet_Queue_Ptrs'(others => NOBUF));

            --  Perform action specific to data buffers

            if Common.Is_Data_Buffer (Cur_Buf) then
               Data.Buffer_Free
                 (Buf      => Data.To_Dbuf_Id (Cur_Buf),
                  Next_Buf => Next_Buf);
            else
               No_Data.Buffer_Free
                 (Buf      => No_Data.To_Rbuf_Id (Cur_Buf),
                  Next_Buf => Next_Buf);
            end if;

            --  Update the count. A single data buffer spanning multiple
            --  physical buffers still counts as 1.

            N_Deallocs := N_Deallocs + 1;

         else
            --  Stop the iteration

            Next_Buf := NOBUF;
         end if;
      end loop;
   end Buffer_Free;

   -----------------------
   -- Buffer_Blind_Free --
   -----------------------

   procedure Buffer_Blind_Free (Buf : Buffer_Id) with
     Refined_Global => (In_Out => (Common.Buf_List,
                                   Data.Free_List,
                                   Data.State,
                                   No_Data.Free_List))
   is
      N_Deallocs : AIP.U8_T;
      pragma Unreferenced (N_Deallocs);
   begin
      pragma Warnings (Off, "unused assignment to ""N_Deallocs""");
      Buffer_Free (Buf, N_Deallocs);
   end Buffer_Blind_Free;

   --------------------
   -- Buffer_Release --
   --------------------

   procedure Buffer_Release (Buf : Buffer_Id) with
     Refined_Global => (In_Out => (Common.Buf_List,
                                   Data.Free_List,
                                   Data.State,
                                   No_Data.Free_List))
   is
      N_Deallocs : AIP.U8_T := 0;
   begin
      --  Keep calling Buffer_Free until it deallocates
      while N_Deallocs = 0 loop
         Buffer_Free (Buf, N_Deallocs);
      end loop;
   end Buffer_Release;

   ----------------
   -- Buffer_Cat --
   ----------------

   procedure Buffer_Cat (Head : Buffer_Id; Tail : Buffer_Id) with
     Refined_Global => (In_Out => Common.Buf_List)
   is
      Cur_Buf, Next_Buf : Buffer_Id;
      Tail_Len          : Data_Length;
   begin
      Cur_Buf  := Head;
      --  Not useful as Head should not be NOBUF and thus the loop always
      --  executed. Cur_Buf initialized anyway to avoid Examiner flow error.

      Next_Buf := Head;
      Tail_Len := Common.Buf_List (Tail).Tot_Len;

      while Next_Buf /= NOBUF loop
         --  Update iterators
         Cur_Buf  := Next_Buf;
         Next_Buf := Common.Buf_List (Cur_Buf).Next;

         --  Add total length of second chain to all totals of first chain
         Common.Buf_List (Cur_Buf).Tot_Len :=
           Common.Buf_List (Cur_Buf).Tot_Len + Tail_Len;
      end loop;

      --  Chain last buffer of Head with first of Tail. Note that no specific
      --  action is done for data buffers, as Head and Tail represent here
      --  two different buffers in the packet chain.
      Common.Buf_List (Cur_Buf).Next := Tail;

      --  Head now points to Tail, but the caller will drop its reference to
      --  Tail, so netto there is no difference to the reference count of Tail.
   end Buffer_Cat;

   ------------------
   -- Buffer_Chain --
   ------------------

   procedure Buffer_Chain (Head : Buffer_Id; Tail : Buffer_Id) with
     Refined_Global => (In_Out => Common.Buf_List)
   is
   begin
      Buffer_Ref (Tail);
      Buffer_Cat (Head, Tail);

      --  Tail is now referenced by Head

   end Buffer_Chain;

   -----------
   -- Empty --
   -----------

   function Empty (Queue : Packet_Queue) return Boolean is
   begin
      return Queue.Head = NOBUF;
   end Empty;

   -----------------
   -- Head_Packet --
   -----------------

   function Head_Packet (Queue : Packet_Queue) return Buffer_Id is
   begin
      return Queue.Head;
   end Head_Packet;

   -----------------
   -- Tail_Packet --
   -----------------

   function Tail_Packet (Queue : Packet_Queue) return Buffer_Id is
   begin
      return Queue.Tail;
   end Tail_Packet;

   -----------------
   -- Packet_Info --
   -----------------

   function Packet_Info (B : Buffer_Id) return System.Address with
     Refined_Global => Common.Buf_List
   is
   begin
      return Common.Buf_List (B).Packet_Info;
   end Packet_Info;

   -------------------
   -- Remove_Packet --
   -------------------

   procedure Remove_Packet
     (Layer : Packet_Layer;
      Queue : in out Packet_Queue;
      Buf   : out Buffer_Id)
   with
     Refined_Global => (In_Out => Common.Buf_List)
   is
   begin
      Buf := Queue.Head;
      if Buf /= NOBUF then
         Queue.Head := Common.Buf_List (Buf).Next_Packet (Layer);

         --  Packet is detached from list: clear its Next_Packet pointer

         Common.Buf_List (Buf).Next_Packet (Layer) := NOBUF;
      end if;

      if Queue.Head = NOBUF then
         Queue.Tail := NOBUF;
      end if;
   end Remove_Packet;

   ---------------------
   -- Set_Packet_Info --
   ---------------------

   procedure Set_Packet_Info (B : Buffer_Id; PI : System.Address) with
     Refined_Global => (In_Out => Common.Buf_List)
   is
   begin
      Common.Buf_List (B).Packet_Info := PI;
   end Set_Packet_Info;

end AIP.Buffers;
