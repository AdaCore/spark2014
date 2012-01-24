------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--         Copyright (C) 2010-2012, Free Software Foundation, Inc.          --
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

   subtype Dbuf_Index is Dbuf_Id range 1 .. Dbuf_Id'Last;
   subtype Dbuf_Count is Dbuf_Index;

   type Buffer is record
      Num         : Dbuf_Count;
      --  Number of buffers in singly linked chain

      Num_No_Jump : Dbuf_Count;
      --  Number of contiguous buffers in singly linked chain from this buffer

      Kind        : Buffers.Data_Buffer_Kind;
      --  Kind of buffer
   end record;

   type Dbuf_Array is array (Dbuf_Index) of Buffer;
   Buf_List : Dbuf_Array;

   ----------------
   -- To_Dbuf_Id --
   ----------------

   function To_Dbuf_Id (Buf : Buffers.Buffer_Id) return Dbuf_Id is
   begin
      return Dbuf_Id (Buf);
   end To_Dbuf_Id;

   ------------------
   -- To_Common_Id --
   ------------------

   function To_Common_Id (Buf : Dbuf_Id) return Buffers.Buffer_Id is
   begin
      return Buffers.Buffer_Id (Buf);
   end To_Common_Id;

   -----------------
   -- Buffer_Init --
   -----------------

   procedure Buffer_Init
   --# global out Data_Array, Buf_List, Free_List;
   is
   begin
      --  First initialize all the memory for buffers to zero, except for
      --  special number fields initialized to one.

      Buf_List := Dbuf_Array'
        (others => Buffer'(Num  => 1, Num_No_Jump => 1,
                           Kind => Buffers.LINK_BUF));

      --  Set special fields to adapt to a singly linked chain of buffers

      for Buf in Dbuf_Index range 1 .. Dbuf_Index'Last - 1 loop
         Buf_List (Buf).Num         := (Dbuf_Index'Last - Buf) + 1;
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
     (Offset : Buffers.Buffer_Length;
      Size   : Buffers.Data_Length;
      Kind   : Buffers.Data_Buffer_Kind;
      Buf    : out Dbuf_Id)
   --# global in out Common.Buf_List, Buf_List, Free_List;
   is
      Requested_Size    : AIP.U16_T;
      Requested_Buffers : Dbuf_Count;

      Remaining_Size    : Buffers.Data_Length;
      --  Remaining size to be allocated

      Cur_Buf, Next_Buf : Dbuf_Id;
      --  Local indices to run over the free list

      Cur_Cbuf : Buffers.Buffer_Id;
      --  Common index for Cur_Buf
   begin
      --  Check that the free-list is not empty

      Support.Verify (Free_List /= Buffers.NOBUF);

      Requested_Size := Offset + Size;
      if Requested_Size = 0 then
         Requested_Buffers := 1;
      else
         Requested_Buffers :=
           Dbuf_Count ((Requested_Size + (Config.Data_Buffer_Size - 1))
                       / Config.Data_Buffer_Size);
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
      Cur_Cbuf       := To_Common_Id (Cur_Buf);

      Next_Buf       := Buf;
      Remaining_Size := Requested_Size;

      --  Allocate buffers in singly linked chain

      for Remaining in reverse Dbuf_Count range 1 .. Requested_Buffers loop
         --  Update iterators

         Cur_Buf  := Next_Buf;
         Cur_Cbuf := To_Common_Id (Cur_Buf);

         if Common.Is_Data_Buffer (Common.Buf_List (Cur_Cbuf).Next) then
            Next_Buf := To_Dbuf_Id (Common.Buf_List (Cur_Cbuf).Next);
         else
            Next_Buf := To_Dbuf_Id (Buffers.NOBUF);
         end if;

         --  Num and Num_No_Jump are as currently defined

         Buf_List (Cur_Buf).Num              := Remaining;
         Buf_List (Cur_Buf).Num_No_Jump      :=
           Dbuf_Count'Min (Buf_List (Cur_Buf).Num_No_Jump, Remaining);

         --  Left offset is zero for all buffers but the first one

         if Remaining = Requested_Buffers then
            Common.Buf_List (Cur_Cbuf).Poffset := Offset;
         else
            Common.Buf_List (Cur_Cbuf).Poffset := 0;
         end if;

         Common.Buf_List (Cur_Cbuf).Tot_Len   :=
           Remaining_Size - Common.Buf_List (Cur_Cbuf).Poffset;

         --# accept F, 41, "Expression is stable";
         case Kind is
            when Buffers.LINK_BUF =>
               --  Length completes offset to buffer size unless not enough
               --  data remaining.

               Common.Buf_List (Cur_Cbuf).Len :=
                 AIP.U16_T'Min (Config.Data_Buffer_Size
                                - Common.Buf_List (Cur_Cbuf).Poffset,
                                Common.Buf_List (Cur_Cbuf).Tot_Len);
            when Buffers.SPLIT_BUF =>
               --  Length is same as total length

               Common.Buf_List (Cur_Cbuf).Len :=
                 Common.Buf_List (Cur_Cbuf).Tot_Len;
         end case;
         --# end accept;

         --  Remaining size decreases by buffer size until last buffer

         if Remaining /= 1 then
            Remaining_Size := Remaining_Size - Config.Data_Buffer_Size;
         end if;

         Buf_List (Cur_Buf).Kind := Kind;

         --  Set reference count

         Common.Buf_List (Cur_Cbuf).Ref := 1;
      end loop;

      --  Remove the allocated buffers from the free list

      Common.Buf_List (Cur_Cbuf).Next := Buffers.NOBUF;
      Free_List                       := Next_Buf;
   end Buffer_Alloc;

   --------------------
   -- Buffer_Payload --
   --------------------

   function Buffer_Payload (Buf : Dbuf_Id) return System.Address
   --# global in Data_Array, Buf_List;
   is
      --# hide Buffer_Payload;  --  Using 'Address
      Buf_Start_Offset : constant Data_Length :=
        Data_Length (Buf - Dbuf_Index'First) * Config.Data_Buffer_Size;
   begin
      return Conversions.Ofs
        (Data_Array (Data_Array'First + Buf_Start_Offset)'Address,
         Integer (Common.Buf_List (To_Common_Id (Buf)).Poffset));
   end Buffer_Payload;

   -----------------
   -- Buffer_Link --
   -----------------

   procedure Buffer_Link (Buf : Dbuf_Id; Next : Dbuf_Id)
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
