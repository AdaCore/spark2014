------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Buffers.Common;
with AIP.Buffers.Data;
with AIP.Buffers.No_Data;
with AIP.Conversions;
with AIP.Support;

package body AIP.Buffers
--# own State is AIP.Buffers.Common.Buf_List,
--#              AIP.Buffers.Data.State, AIP.Buffers.Data.Free_List,
--#              AIP.Buffers.No_Data.State, AIP.Buffers.No_Data.Free_List;
is
   --------------------
   -- Is_Data_Buffer --
   --------------------

   --  Early definition of Is_Data_Buffer out of alphabetical order, because
   --  function is called in other subprograms

   function Is_Data_Buffer (Buf : Buffer_Id) return Boolean is
   begin
      --  Decision between data buffer and no-data buffer should not apply to
      --  null buffer, which is both
      Support.Verify (Buf /= NOBUF);

      return Buf <= Config.Data_Buffer_Num;
   end Is_Data_Buffer;

   -------------------
   -- Append_Packet --
   -------------------

   procedure Append_Packet (L : in out Packet_List; Buf : Buffer_Id)
   --# global in out Common.Buf_List;
   is
   begin
      if L.Tail /= NOBUF then
         Common.Buf_List (L.Tail).Next_Packet := Buf;
         L.Tail := Buf;
      else
         L.Head := Buf;
         L.Tail := Buf;
      end if;
   end Append_Packet;

   -----------------
   -- Buffer_Copy --
   -----------------

   procedure Buffer_Copy
     (Dst : Buffer_Id;
      Src : Buffer_Id;
      Len : AIP.U16_T;
      Err : out AIP.Err_T)
   --# global in out Data.State, No_Data.State;
   is
      --# hide Buffer_Copy;

      type Data is array (1 .. Len) of U8_T;

      Src_Data : Data;
      for Src_Data'Address use Buffer_Payload (Src);
      pragma Import (Ada, Src_Data);

      Dst_Data : Data;
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

   procedure Buffer_Init
   --# global out Common.Buf_List,
   --#            Data.State, Data.Free_List,
   --#            No_Data.State, No_Data.Free_List;
   is
   begin
      --  Zero out all the memory for common buffers data structure to zero

      Common.Buf_List :=
        Common.Buffer_Array'
          (others =>
               Common.Buffer'(Next => NOBUF, Next_Packet => NOBUF,
                              Len  => 0, Tot_Len => 0, Poffset => 0,
                              Ref  => 0));

      --  Construct a singly linked chain of common buffer structures,
      --  then Initialize data/no-data specific structures

      for Buf in Buffer_Index range 1 .. Buffer_Index'Last - 1 loop
         Common.Buf_List (Buf).Next := Buf + 1;
      end loop;

      No_Data.Buffer_Init;
      Data.Buffer_Init;
   end Buffer_Init;

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Kind   : Data_Buffer_Kind;
      Offset : Buffer_Length;
      Size   : Data_Length;
      Buf    : out Buffer_Id)
   --# global in out Common.Buf_List, Data.State, Data.Free_List;
   is
   begin
      Data.Buffer_Alloc
        (Kind   => Kind,
         Offset => Offset,
         Size   => Size,
         Buf    => Buf);
   end Buffer_Alloc;

   ----------------------
   -- Ref_Buffer_Alloc --
   ----------------------

   procedure Ref_Buffer_Alloc
     (Ref    : System.Address;
      Offset : Buffer_Length;
      Size   : Data_Length;
      Buf    : out Buffer_Id)
   --# global in out Common.Buf_List, No_Data.State, No_Data.Free_List;
   is
      No_Data_Buf : No_Data.Buffer_Id;
   begin
      No_Data.Buffer_Alloc
        (Ref    => Ref,
         Offset => Offset,
         Size   => Size,
         Buf    => No_Data_Buf);
      Buf := No_Data.To_Common_Id (No_Data_Buf);
   end Ref_Buffer_Alloc;

   ----------------
   -- Buffer_Len --
   ----------------

   function Buffer_Len (Buf : Buffer_Id) return AIP.U16_T
   --# global in Common.Buf_List;
   is
   begin
      return Common.Buf_List (Buf).Len;
   end Buffer_Len;

   -----------------
   -- Buffer_Tlen --
   -----------------

   function Buffer_Tlen (Buf : Buffer_Id) return AIP.U16_T
   --# global in Common.Buf_List;
   is
   begin
      return Common.Buf_List (Buf).Tot_Len;
   end Buffer_Tlen;

   -----------------
   -- Buffer_Next --
   -----------------

   function Buffer_Next (Buf : Buffer_Id) return Buffer_Id
   --# global in Common.Buf_List;
   is
   begin
      return Common.Buf_List (Buf).Next;
   end Buffer_Next;

   --------------------
   -- Buffer_Payload --
   --------------------

   function Buffer_Payload (Buf : Buffer_Id) return System.Address
   --# global in Data.State, No_Data.State;
   is
      Result : System.Address;
   begin
      if Is_Data_Buffer (Buf) then
         Result := Data.Buffer_Payload (Buf);
      else
         Result := No_Data.Buffer_Payload (No_Data.To_Ref_Id (Buf));
      end if;
      return Result;
   end Buffer_Payload;

   --------------------
   -- Buffer_Poffset --
   --------------------

   function Buffer_Poffset (Buf : Buffer_Id) return AIP.U16_T
   --# global in Common.Buf_List;
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
   --# global in out Common.Buf_List;
   is
      Offset : AIP.U16_T;
   begin
      Offset := AIP.U16_T (abs (Bump));
      Err    := AIP.NOERR;

      --  Check that we are not going to move off the buffer data

      if Bump < 0 then

         --  Moving forward - not beyond end of buffer data

         Support.Verify_Or_Err
           (Common.Buf_List (Buf).Len >= Offset, Err, AIP.ERR_MEM);

      elsif Bump > 0 then

         --  Moving backward - no before start of buffer data

         Support.Verify_Or_Err
           (Common.Buf_List (Buf).Poffset - Offset >= 0, Err, AIP.ERR_MEM);
      end if;

      --  Adjust payload offset and lengths if all went fine

      if AIP.No (Err) then

         if Bump >= 0 then
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
   --# global in out Common.Buf_List; in Data.State, No_Data.State;
   is
      Pload_Shift : AIP.S16_T;
      --  Amount by which we need to shift the payload pointer. Positive
      --  for a move forward.
   begin
      Pload_Shift
        := AIP.S16_T (Conversions.Diff (Pload, Buffer_Payload (Buf)));
      Buffer_Header (Buf, -Pload_Shift, Err);
   end Buffer_Set_Payload;

   ----------------
   -- Buffer_Ref --
   ----------------

   procedure Buffer_Ref (Buf : Buffer_Id)
   --# global in out Common.Buf_List;
   is
   begin
      Common.Buf_List (Buf).Ref := Common.Buf_List (Buf).Ref + 1;
   end Buffer_Ref;

   -----------------
   -- Buffer_Free --
   -----------------

   procedure Buffer_Free (Buf : Buffer_Id; N_Deallocs : out AIP.U8_T)
   --# global in out Common.Buf_List, Data.State,
   --#               Data.Free_List, No_Data.Free_List;
   is
      Cur_Buf, Next_Buf : Buffer_Id;
      Free_List         : Buffer_Index;
   begin
      Next_Buf   := Buf;
      N_Deallocs := 0;

      while Next_Buf /= NOBUF loop

         --  Update iterators

         Cur_Buf  := Next_Buf;
         Next_Buf := Common.Buf_List (Cur_Buf).Next;

         --  Store head of appropriate free-list in Free_List

         if Is_Data_Buffer (Cur_Buf) then
            Free_List := Data.Free_List;
         else
            Free_List := No_Data.To_Common_Id (No_Data.Free_List);
         end if;

         --  Decrease reference count

         Common.Buf_List (Cur_Buf).Ref := Common.Buf_List (Cur_Buf).Ref - 1;

         --  If reference count reaches zero, deallocate buffer

         if Common.Buf_List (Cur_Buf).Ref = 0 then
            N_Deallocs := N_Deallocs + 1;

            --  Link to the head of the free-list

            Common.Buf_List (Cur_Buf).Next := Free_List;

            --  Perform link actions specific to data buffers

            if Is_Data_Buffer (Cur_Buf) then
               Data.Buffer_Link (Cur_Buf, Free_List);
            end if;

            --  Push to the head of the appropriate free-list

            if Is_Data_Buffer (Cur_Buf) then
               Data.Free_List    := Cur_Buf;
            else
               No_Data.Free_List := No_Data.To_Ref_Id (Cur_Buf);
            end if;
         else
            --  Stop the iteration

            Next_Buf                       := NOBUF;
         end if;
      end loop;
   end Buffer_Free;

   -----------------------
   -- Buffer_Blind_Free --
   -----------------------

   procedure Buffer_Blind_Free (Buf : Buffer_Id)
   --# global in out Common.Buf_List, Data.State,
   --#               Data.Free_List, No_Data.Free_List;
   is
      N_Deallocs : AIP.U8_T;
      pragma Unreferenced (N_Deallocs);
   begin
      --# accept F, 10, N_Deallocs, "Assignment is ineffective";
      Buffer_Free (Buf, N_Deallocs);
      --# end accept;
      --# accept F, 33, N_Deallocs,
      --#               "The variable is neither referenced nor exported";
   end Buffer_Blind_Free;

   --------------------
   -- Buffer_Release --
   --------------------

   procedure Buffer_Release (Buf : Buffer_Id)
   --# global in out Common.Buf_List, Data.State,
   --#               Data.Free_List, No_Data.Free_List;
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

   procedure Buffer_Cat (Head : Buffer_Id; Tail : Buffer_Id)
   --# global in out Common.Buf_List;
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

   procedure Buffer_Chain (Head : Buffer_Id; Tail : Buffer_Id)
   --# global in out Common.Buf_List;
   is
   begin
      Buffer_Cat (Head, Tail);
      --  Tail is now referenced by Head
      Buffer_Ref (Tail);
   end Buffer_Chain;

   -----------
   -- Empty --
   -----------

   function Empty (L : Packet_List) return Boolean is
   begin
      return L.Head = NOBUF;
   end Empty;

   -------------------
   -- Remove_Packet --
   -------------------

   procedure Remove_Packet (L : in out Packet_List; Buf : out Buffer_Id)
   --# global in Common.Buf_List;
   is
   begin
      Buf := L.Head;
      if L.Head /= NOBUF then
         L.Head := Common.Buf_List (Buf).Next_Packet;
      end if;
      if L.Head = NOBUF then
         L.Tail := NOBUF;
      end if;
   end Remove_Packet;

end AIP.Buffers;
