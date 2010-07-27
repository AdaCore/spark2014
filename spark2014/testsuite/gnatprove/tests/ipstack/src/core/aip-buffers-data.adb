------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Support;
with AIP.Conversions;
with AIP.Buffers.Common;

package body AIP.Buffers.Data
--# own State is Data_Array, Buf_List;
is
   --  All data is stored in a statically allocated array Data_Array, while
   --  data structures to manage the allocation of pieces of this array to
   --  buffers are stored in another statically allocated array Buffers.

   --  This division allows the allocation of contiguous pieces of the
   --  Data_Array array to a single buffer, so as to simulate the allocation
   --  of a single chunk of memory, which is required for SPLIT_BUF buffers.

   subtype Data_Index is Buffers.Data_Length range
     1 .. Config.Data_Buffer_Size * Config.Data_Buffer_Num;
   type Data_Array_Type is array (Data_Index) of Buffers.Elem;

   Data_Array : Data_Array_Type;

   subtype Buffer_Index is AIP.U16_T range 1 .. Config.Data_Buffer_Num;
   subtype Buffer_Count is Buffer_Index;
   --  What is the relationship between Buffer_Index and Buffer_Id???

   type Buffer is record
      Num          : Buffer_Count;
      --  Number of buffers in singly linked chain

      Num_No_Jump  : Buffer_Count;
      --  Number of contiguous buffers in singly linked chain from this buffer

      Left_Offset  : Buffers.Buffer_Length;
      --  Offset to get to the position of the actual data in the buffer

      Kind         : Buffers.Data_Buffer_Kind;
      --  Kind of buffer
   end record;

   type Buffer_Array is array (Buffer_Index) of Buffer;

   Buf_List : Buffer_Array;

   -----------------
   -- Buffer_Init --
   -----------------

   procedure Buffer_Init
   --# global out Data_Array, Buf_List, Free_List;
   is
   begin
      --  First initialize all the memory for buffers to zero, except for
      --  special number fields initialized to one.

      Buf_List := Buffer_Array'
        (others => Buffer'(Num  => 1, Num_No_Jump => 1, Left_Offset => 0,
                           Kind => Buffers.LINK_BUF));

      --  Set special fields to adapt to a singly linked chain of buffers

      for Buf in Buffer_Index range 1 .. Buffer_Index'Last - 1 loop
         Buf_List (Buf).Num         := (Buffer_Index'Last - Buf) + 1;
         Buf_List (Buf).Num_No_Jump := Buf_List (Buf).Num;
      end loop;

      --  Make the head of the free-list point to the first buffer

      Free_List := 1;

      --  Intentionally leave Data_Array not initialized
      --# accept F, 32, Data_Array,
      --#               "The variable is neither imported nor defined";
      --# accept F, 31, Data_Array,
      --#           "The variable is exported but not (internally) defined";
   end Buffer_Init;

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Offset :     Buffers.Buffer_Length;
      Size   :     Buffers.Data_Length;
      Kind   :     Buffers.Data_Buffer_Kind;
      Buf    : out Buffer_Id)
   --# global in out Common.Buf_List, Buf_List, Free_List;
   is
      Requested_Size    : AIP.U16_T;
      Requested_Buffers : AIP.U16_T;
      Cur_Buf, Next_Buf : Buffer_Id;

      Remaining_Size    : Buffers.Data_Length;
      --  Remaining size to be allocated
   begin
      --  Check that the free-list is not empty

      Support.Verify (Free_List /= Buffers.NOBUF);

      Requested_Size := Offset + Size;
      if Requested_Size = 0 then
         Requested_Buffers := 1;
      else
         Requested_Buffers :=
           (Requested_Size + (Config.Data_Buffer_Size - 1))
           / Config.Data_Buffer_Size;
      end if;

      --  Check that the requested number of buffers are available, and that
      --  they form a contiguous chain of buffers for Kind = SPLIT_BUF.

      case Kind is
         when Buffers.LINK_BUF =>
            Support.Verify (Requested_Buffers <= Buf_List (Free_List).Num);
         when Buffers.SPLIT_BUF =>
            Support.Verify
              (Requested_Buffers <= Buf_List (Free_List).Num_No_Jump);
      end case;

      --  Pop the head of the free-list

      Buf            := Free_List;

      --  The following assignment is useless because loop always executes,
      --  but is added to ensure Cur_Buf is initialized anyway.
      --  Does this mean SPARK doesn't notice that the loop always runs???

      Cur_Buf        := Buf;

      Next_Buf       := Buf;
      Remaining_Size := Requested_Size;

      --  Allocate buffers in singly linked chain

      for Remaining in reverse AIP.U16_T range 1 .. Requested_Buffers loop
         --  Update iterators

         Cur_Buf                             := Next_Buf;
         Next_Buf                            := Common.Buf_List (Cur_Buf).Next;

         --  Num and Num_No_Jump are as currently defined

         Buf_List (Cur_Buf).Num              := Remaining;
         Buf_List (Cur_Buf).Num_No_Jump      :=
           Buffer_Count'Min (Buf_List (Cur_Buf).Num_No_Jump, Remaining);

         --  Left offset is zero for all buffers but the first one

         if Remaining = Requested_Buffers then
            Buf_List (Cur_Buf).Left_Offset   := Offset;
         else
            Buf_List (Cur_Buf).Left_Offset   := 0;
         end if;

         Common.Buf_List (Cur_Buf).Tot_Len   :=
           Remaining_Size - Buf_List (Cur_Buf).Left_Offset;

         --# accept F, 41, "Expression is stable";
         case Kind is
            when Buffers.LINK_BUF =>
               --  Length completes offset to buffer size unless not enough
               --  data remaining.

               Common.Buf_List (Cur_Buf).Len :=
                 AIP.U16_T'Min (Config.Data_Buffer_Size
                                - Buf_List (Cur_Buf).Left_Offset,
                                Common.Buf_List (Cur_Buf).Tot_Len);
            when Buffers.SPLIT_BUF =>
               --  Length is same as total length

               Common.Buf_List (Cur_Buf).Len :=
                 Common.Buf_List (Cur_Buf).Tot_Len;
         end case;
         --# end accept;

         --  Remaining size decreases by buffer size until last buffer

         if Remaining /= 1 then
            Remaining_Size := Remaining_Size - Config.Data_Buffer_Size;
         end if;

         Buf_List (Cur_Buf).Kind := Kind;

         --  Set reference count

         Common.Buf_List (Cur_Buf).Ref := 1;
      end loop;

      --  Remove the allocated buffers from the free list

      Common.Buf_List (Cur_Buf).Next := Buffers.NOBUF;
      Free_List                      := Next_Buf;
   end Buffer_Alloc;

   --------------------
   -- Buffer_Payload --
   --------------------

   function Buffer_Payload (Buf : Buffer_Id) return System.Address
   --# global in Data_Array, Buf_List;
   is
      --# hide Buffer_Payload;  --  Hidden because of 'Address attribute
      Buf_Start_Offset : constant Data_Length :=
                           (Buf - Buffer_Index'First)
                             * Config.Data_Buffer_Size;
   begin
      return Conversions.Ofs
        (Data_Array (Data_Array'First + Buf_Start_Offset)'Address,
         Integer (Buf_List (Buf).Left_Offset));
   end Buffer_Payload;

   ------------------------
   -- Buffer_Set_Payload --
   ------------------------

   procedure Buffer_Set_Payload
     (Buf   : Buffer_Id;
      Pload : System.Address;
      Err   : out AIP.Err_T)
   --# global in out Data_Array, Buf_List;
   is
      Pload_Shift : AIP.S16_T;
      --  Amount by which we need to shift the payload pointer. Positive
      --  for a move forward.
   begin
      Pload_Shift
        := AIP.S16_T (Conversions.Diff (Pload, Buffer_Payload (Buf)));
      Buffer_Header (Buf, -Pload_Shift, Err);
   end Buffer_Set_Payload;

   --------------------
   -- Buffer_Poffset --
   --------------------

   function Buffer_Poffset (Buf : Buffer_Id) return AIP.U16_T
   --# global in Buf_List;
   is
   begin
      return Buf_List (Buf).Left_Offset;
   end Buffer_Poffset;

   -------------------
   -- Buffer_Header --
   -------------------

   procedure Buffer_Header
     (Buf  : Buffer_Id;
      Bump : AIP.S16_T;
      Err  : out AIP.Err_T)
   --# global in out Buf_List;
   is
      Offset : AIP.U16_T;
   begin
      Offset := AIP.U16_T (abs (Bump));

      --  Check that we are not going to move off the beginning of the buffer

      if Bump >= 0 then
         Support.Verify_Or_Err
           (Buf_List (Buf).Left_Offset - Offset >= 0, Err, AIP.ERR_MEM);
      end if;

      if Err = AIP.NOERR then
         if Bump >= 0 then
            Buf_List (Buf).Left_Offset := Buf_List (Buf).Left_Offset - Offset;
         else
            Buf_List (Buf).Left_Offset := Buf_List (Buf).Left_Offset + Offset;
         end if;
      end if;
   end Buffer_Header;

   -----------------
   -- Buffer_Link --
   -----------------

   procedure Buffer_Link (Buf : Buffer_Id; Next : Buffer_Id)
   --# global in out Buf_List;
   is
   begin
      --  Update Num and Num_No_Jump fields only

      Buf_List (Buf).Num            := Buf_List (Next).Num + 1;
      if Next = Buf + 1 then
         Buf_List (Buf).Num_No_Jump := Buf_List (Next).Num_No_Jump + 1;
      else
         Buf_List (Buf).Num_No_Jump := 1;
      end if;
   end Buffer_Link;

end AIP.Buffers.Data;
