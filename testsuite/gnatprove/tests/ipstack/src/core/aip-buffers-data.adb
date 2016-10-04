------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2015, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with AIP.Support;
with AIP.Conversions;
with AIP.Buffers.Common;

package body AIP.Buffers.Data with
  Refined_State => (State => (Data_Array, Buf_List))
is
   --  All data is stored in a statically allocated array Data_Array, while
   --  data structures to manage the allocation of pieces of this array to
   --  buffers are stored in another statically allocated array Buffers.

   --  This division allows the allocation of contiguous pieces of the
   --  Data_Array array to a single buffer, so as to simulate the allocation
   --  of a single chunk of memory, which is required for SPLIT_BUF buffers.

   type Data_Offset is range AIP.S32_T'First .. AIP.S32_T'Last;
   subtype Data_Index is Data_Offset
     range 1 .. Config.Data_Buffer_Size * Config.Data_Buffer_Num;
   type Data_Array_Type is array (Data_Index) of Buffers.Elem;

   Data_Array : Data_Array_Type;

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

   -------------------
   -- Next_Data_Buf --
   -------------------

   function Next_Data_Buf (Buf : Dbuf_Id) return Dbuf_Id is
   begin
      return To_Dbuf_Id (Common.Buf_List (To_Common_Id (Buf)).Next);
   end Next_Data_Buf;

   --------------------------------------
   -- Advance_To_Next_Contiguous_Block --
   --------------------------------------

   procedure Advance_To_Next_Contiguous_Block
     (Buf      : in out Dbuf_Id;
      Prev_Buf : out Dbuf_Id;
      Num      : out Dbuf_Count)
   with
     Refined_Global => (Input => (Buf_List, Common.Buf_List))
   is
      Tmp_Buf : Dbuf_Id;
      Tmp_Num : Dbuf_Count_Or_Null;

   begin
      Tmp_Buf := Buf;
      Tmp_Num := 0;

      --  Start with reaching the last buffer in the contiguous block to which
      --  Buf belongs.

      while Buf_List (Tmp_Buf).Num_No_Jump /= 1 loop
         Tmp_Buf := Next_Data_Buf (Tmp_Buf);
         Tmp_Num := Tmp_Num + 1;
      end loop;

      --  The following block is the one desired (possibly NOBUF)

      Prev_Buf := Tmp_Buf;
      Buf      := Next_Data_Buf (Tmp_Buf);
      Tmp_Num  := Tmp_Num + 1;
      Num      := Tmp_Num;
   end Advance_To_Next_Contiguous_Block;

   ------------------------------------
   -- Insert_Contiguous_In_Free_List --
   ------------------------------------

   procedure Insert_Contiguous_In_Free_List (Buf : Dbuf_Id; Num : Dbuf_Count)
   with
     Refined_Global  => (In_Out => (Buf_List, Common.Buf_List, Free_List))
   is
      Last_Buf : Dbuf_Id;
      --  Last buffer to be inserted

      Free_Buf : Dbuf_Id;
      --  Temporary buffer

      Insert_Buf, Prev_Insert_Buf : Dbuf_Id;
      --  Buffers pointing respectively at the place to insert Buf, and the
      --  previous buffer in the free list.

      Free_Count : Dbuf_Count;
      --  Number of buffers to be added to some counter components

   begin
      --  Identify the last buffer to be inserted, and verify that the buffers
      --  to insert are indeed contiguous.

      Last_Buf := Buf;
      for J in Dbuf_Count range 1 .. Num - 1 loop
         Last_Buf := Next_Data_Buf (Last_Buf);
         Support.Verify (Last_Buf = Buf + J);
      end loop;

      --  Set next of last buffer to NOBUF, to be modified in some cases in the
      --  following.

      Common.Buf_List (To_Common_Id (Last_Buf)).Next := Buffers.NOBUF;

      --  Set an initial value to the Num and Num_No_Jump components for the
      --  buffers to insert.

      Free_Buf := Buf;
      for Remaining in reverse Dbuf_Count range 1 .. Num loop
         Buf_List (Free_Buf).Num         := Remaining;
         Buf_List (Free_Buf).Num_No_Jump := Remaining;
         Free_Buf := Next_Data_Buf (Free_Buf);
      end loop;

      --  If the free list is empty, simply set Buf as its head

      if Free_List = Buffers.NOBUF then
         Free_List := Buf;

      --  If possible, insert at the head of the free list

      elsif Num <= Buf_List (Free_List).Num_No_Jump then

         --  Update the Num component for the buffers to insert

         Free_Count := Buf_List (Free_List).Num;
         Free_Buf := Buf;
         for J in Dbuf_Count range 1 .. Num loop
            Buf_List (Free_Buf).Num := Buf_List (Free_Buf).Num + Free_Count;
            Free_Buf := Next_Data_Buf (Free_Buf);
         end loop;

         --  Insert buffers in front of free list

         Common.Buf_List (To_Common_Id (Last_Buf)).Next :=
           To_Common_Id (Free_List);
         Free_List := Buf;

      --  Otherwise, insert in the middle or at the end of the free list

      else
         --  Dummy initial value of Prev_Insert_Buf to avoid SPARK flow
         --  errors later on. Prev_Insert_Buf is always set by the call
         --  to Advance_To_Next_Contiguous_Block.

         Prev_Insert_Buf := Buffers.NOBUF;

         --  Locate the place to insert the buffers. Note that Insert_Buf might
         --  be NOBUF after the loop, if we reach the end of the free list.

         Insert_Buf := Free_List;
         while Insert_Buf /= Buffers.NOBUF
           and then Buf_List (Insert_Buf).Num_No_Jump < Num
         loop
            pragma Warnings (Off, "unused assignment to ""Free_Count""");
            Advance_To_Next_Contiguous_Block (Buf      => Insert_Buf,
                                              Prev_Buf => Prev_Insert_Buf,
                                              Num      => Free_Count);
            pragma Warnings (On, "unused assignment to ""Free_Count""");
         end loop;

         --  Update the Num component for the previous buffers in the free list

         Free_Buf := Free_List;
         while Free_Buf /= Insert_Buf loop
            Buf_List (Free_Buf).Num := Buf_List (Free_Buf).Num + Num;
            Free_Buf := Next_Data_Buf (Free_Buf);
         end loop;

         --  If needed, update the Num component for the buffers to insert

         if Insert_Buf /= Buffers.NOBUF then
            Free_Count := Buf_List (Insert_Buf).Num;
            Free_Buf := Buf;
            for J in Dbuf_Count range 1 .. Num loop
               Buf_List (Free_Buf).Num := Buf_List (Free_Buf).Num + Free_Count;
               Free_Buf := Next_Data_Buf (Free_Buf);
            end loop;
         end if;

         --  Insert buffers in free list

         Common.Buf_List (To_Common_Id (Prev_Insert_Buf)).Next :=
           To_Common_Id (Buf);
         Common.Buf_List (To_Common_Id (Last_Buf)).Next :=
           To_Common_Id (Insert_Buf);
      end if;
   end Insert_Contiguous_In_Free_List;

   ---------------------------
   -- Remove_From_Free_List --
   ---------------------------

   procedure Remove_From_Free_List (Buf : Dbuf_Id; Num : Dbuf_Count) with
     Refined_Global => (In_Out => (Buf_List, Common.Buf_List, Free_List))
   is
      Last_Buf_In_Prev_Block  : Dbuf_Id;
      --  Last buffer in contiguous block preceding Buf, if any

      First_Buf_Not_Removed   : Dbuf_Id;
      --  First buffer following the removed ones, if any

      First_Buf_In_Next_Block : Dbuf_Id;
      --  First buffer in the contiguous block following the removed buffers,
      --  if any.

      First_Buf_Not_Removed_Starts_New_Block : Boolean;
      --  Whether the buffer First_Buf_Not_Removed starts a contiguous block

      Temp_Removed_Buffers : Dbuf_Count_Or_Null;
      --  Number of buffers temporarily removed

      Free_Buf : Dbuf_Id;
      --  Temporary buffer

   begin
      --  1. Identify relevant buffers in the free list

      --  Retrieve last buffer preceding Buf. This should be either NOBUF or
      --  the last buffer in a contiguous block of buffers.

      if Buf = Free_List then
         Last_Buf_In_Prev_Block := Buffers.NOBUF;
      else
         Last_Buf_In_Prev_Block := Free_List;
         while Next_Data_Buf (Last_Buf_In_Prev_Block) /= Buf loop
            Last_Buf_In_Prev_Block := Next_Data_Buf (Last_Buf_In_Prev_Block);
         end loop;
      end if;

      --  Dummy initial value of First_Buf_Not_Removed_Starts_New_Block
      --  to avoid SPARK flow errors later on.
      --  First_Buf_Not_Removed_Starts_New_Block is always set by the loop
      --  that follows.

      First_Buf_Not_Removed_Starts_New_Block := False;

      --  Retrieve first buffer after Num buffers from Buf. This can be NOBUF.

      First_Buf_Not_Removed := Buf;
      for J in Dbuf_Count range 1 .. Num loop

         --  Detect whether the first buffer not removed starts a contiguous
         --  blocks by looking at the buffer preceding it.

         if J = Num then
            First_Buf_Not_Removed_Starts_New_Block :=
              (Buf_List (First_Buf_Not_Removed).Num_No_Jump = 1);
         end if;

         First_Buf_Not_Removed := Next_Data_Buf (First_Buf_Not_Removed);
      end loop;

      --  Retrieve first buffer starting a new block of contiguous buffer after
      --  the removed ones.

      Temp_Removed_Buffers    := 0;
      First_Buf_In_Next_Block := First_Buf_Not_Removed;
      if not First_Buf_Not_Removed_Starts_New_Block then

         --  Start with reaching the last buffer in the contiguous block to
         --  which First_Buf_Not_Removed belongs.

         while Buf_List (First_Buf_In_Next_Block).Num_No_Jump /= 1 loop
            Temp_Removed_Buffers    := Temp_Removed_Buffers + 1;
            First_Buf_In_Next_Block := Next_Data_Buf (First_Buf_In_Next_Block);
         end loop;

         --  The following block is the one desired

         Temp_Removed_Buffers    := Temp_Removed_Buffers + 1;
         First_Buf_In_Next_Block := Next_Data_Buf (First_Buf_In_Next_Block);
      end if;

      --  2. Restore the free list ordering property and structure

      --  Start by removing temporarily buffers between First_Buf_Not_Removed
      --  (included) and First_Buf_In_Next_Block (excluded).

      --  First, set appropriately the Num component (Num_No_Jump is fine)

      Free_Buf := Free_List;
      while Free_Buf /= Buf loop
         Buf_List (Free_Buf).Num :=
           Buf_List (Free_Buf).Num - Num - Temp_Removed_Buffers;
         Free_Buf := Next_Data_Buf (Free_Buf);
      end loop;

      --  Then, if needed, link the buffers Last_Buf_In_Prev_Block and
      --  First_Buf_In_Next_Block.

      if Last_Buf_In_Prev_Block /= Buffers.NOBUF then
         Common.Buf_List (To_Common_Id (Last_Buf_In_Prev_Block)).Next :=
           To_Common_Id (First_Buf_In_Next_Block);
      end if;

      --  Finally, set the free list head

      if Free_List = Buf then
         Free_List := First_Buf_In_Next_Block;
      end if;

      --  Continue by inserting the removed buffers in the free list, if any

      if Temp_Removed_Buffers > 0 then
         Insert_Contiguous_In_Free_List (Buf => First_Buf_Not_Removed,
                                         Num => Temp_Removed_Buffers);
      end if;
   end Remove_From_Free_List;

   ---------------------------------------
   -- Extract_Contiguous_From_Free_List --
   ---------------------------------------

   procedure Extract_Contiguous_From_Free_List
     (Buf : in out Dbuf_Id;
      Num : in out Dbuf_Count)
   with
       Refined_Global => (In_Out => (Buf_List, Common.Buf_List, Free_List))
   is
      Last_Buf : Dbuf_Id;
      --  Last buffer to be inserted

      Free_Buf, Start_Buf, End_Buf : Dbuf_Id;
      --  Temporary buffer

      Free_Count : Dbuf_Count;
      --  Temporary count

      Prev_Buf, Next_Buf : Dbuf_Id;
      --  Buffers starting the previous and next contiguous blocks in the free
      --  list, if any.

      Prev_Num, Next_Num : Dbuf_Count_Or_Null;
      --  Length of the previous and next contiguous blocks in the free list,
      --  if any.

   begin
      --  Identify the last buffer to be inserted, and verify that the buffers
      --  to insert are indeed contiguous.

      Last_Buf := Buf;
      for J in Dbuf_Count range 1 .. Num - 1 loop
         Last_Buf := Next_Data_Buf (Last_Buf);
         Support.Verify (Last_Buf = Buf + J);
      end loop;

      --  Locate the previous and next contiguous blocks in the free list, if
      --  any.

      Free_Buf := Free_List;
      Prev_Buf := Buffers.NOBUF;
      Next_Buf := Buffers.NOBUF;
      Prev_Num := 0;
      Next_Num := 0;
      while Free_Buf /= Buffers.NOBUF loop
         Start_Buf := Free_Buf;

         --  Compute information on contiguous block starting at Start_Buf

         Advance_To_Next_Contiguous_Block (Buf      => Free_Buf,
                                           Prev_Buf => End_Buf,
                                           Num      => Free_Count);

         --  Recognize the preceding contiguous block. Note that it is always
         --  fine to subtract 1 from a Dbuf_Id that is not NOBUF.

         if End_Buf = Buf - 1 then
            Prev_Buf := Start_Buf;
            Prev_Num := Free_Count;
         end if;

         --  Recognize the following contiguous block. Note that it is always
         --  fine to subtract 1 from a Dbuf_Id that is not NOBUF.

         if Last_Buf = Start_Buf - 1 then
            Next_Buf := Start_Buf;
            Next_Num := Free_Count;
         end if;
      end loop;

      --  Remove the preceding and following contiguous blocks from the free
      --  list, if any.

      if Prev_Buf /= Buffers.NOBUF then
         Remove_From_Free_List (Prev_Buf, Prev_Num);
      end if;

      if Next_Buf /= Buffers.NOBUF then
         Remove_From_Free_List (Next_Buf, Next_Num);
      end if;

      --  Link together the preceding contiguous block, the block to insert and
      --  the following contiguous block.

      if Prev_Buf /= Buffers.NOBUF then
         Common.Buf_List (To_Common_Id (Buf - 1)).Next := To_Common_Id (Buf);
      end if;

      if Next_Buf /= Buffers.NOBUF then
         Common.Buf_List (To_Common_Id (Last_Buf)).Next :=
           To_Common_Id (Next_Buf);
      end if;

      --  Update the parameters

      if Prev_Buf /= Buffers.NOBUF then
         Buf := Prev_Buf;
      end if;

      Num := (Prev_Num + Num) + Next_Num;
   end Extract_Contiguous_From_Free_List;

   -------------------------
   -- Insert_In_Free_List --
   -------------------------

   procedure Insert_In_Free_List (Buf : Dbuf_Id; Num : Dbuf_Count) with
     Refined_Global => (In_Out => (Buf_List, Common.Buf_List, Free_List))
   is
      Free_Buf, First_Buf, Last_Buf : Dbuf_Id;
      --  Temporary buffers

      Free_Count, Extracted_Free_Count : Dbuf_Count;
      --  Number of contiguous buffers to insert

      Num_To_Insert : Dbuf_Count_Or_Null;
      --  Remaining number of buffers to insert

   begin
      First_Buf := Buf;
      Num_To_Insert := Num;

      --  Insert buffers by contiguous blocks

      while Num_To_Insert > 0 loop

         --  Locate the first buffer of the next contiguous block, and count
         --  the number of buffers in the current block from First_Buf. The
         --  value assigned to Last_Buf by the call to
         --  Advance_To_Next_Contiguous_Block is ignored.

         Free_Buf := First_Buf;
         pragma Warnings (Off, "unused assignment to ""Last_Buf""");
         Advance_To_Next_Contiguous_Block (Buf      => Free_Buf,
                                           Prev_Buf => Last_Buf,
                                           Num      => Free_Count);
         pragma Warnings (On, "unused assignment to ""Last_Buf""");

         --  Adjust the number of buffers to insert, which might be smaller
         --  than the number of contiguous buffers from First_Buf.

         Free_Count := Dbuf_Count'Min (Num_To_Insert, Free_Count);

         --  Compute a contiguous block that includes the Free_Count buffers
         --  starting from First_Buf, and possibly preceding and following
         --  buffers from the free list, so that inserting this contiguous
         --  block in the modified free list does not lead to fragmentation.

         Extracted_Free_Count := Free_Count;
         Extract_Contiguous_From_Free_List (First_Buf, Extracted_Free_Count);

         --  Actually insert the next contiguous block of buffers

         Insert_Contiguous_In_Free_List (First_Buf, Extracted_Free_Count);

         --  Update local values for next iteration

         Num_To_Insert := Num_To_Insert - Free_Count;
         First_Buf := Free_Buf;
      end loop;
   end Insert_In_Free_List;

   -----------------
   -- Buffer_Init --
   -----------------

   procedure Buffer_Init with
     Refined_Global => (Output => (Buf_List, Data_Array, Free_List))
   is
      pragma Annotate (GNATprove, Intentional,
                       "unused",
                       "Data_Array not initialized for efficiency");
      pragma Annotate (GNATprove, Intentional,
                       "not initialized",
                       "Data_Array not initialized for efficiency");
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

      Free_List := Buf_List'First;
   end Buffer_Init;

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Offset : Buffers.Buffer_Length;
      Size   : Buffers.Data_Length;
      Kind   : Buffers.Data_Buffer_Kind;
      Buf    : out Dbuf_Id)
   with
     Refined_Global => (In_Out => (Buf_List, Common.Buf_List, Free_List))
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

         --  Allocate LINK_BUF buffers at the start of the free-list

         when Buffers.LINK_BUF =>
            Buf := Free_List;
            Support.Verify (Requested_Buffers <= Buf_List (Buf).Num);

         --  Allocate SPLIT_BUF buffers at the first place in the free list
         --  which holds enough contiguous space.

         when Buffers.SPLIT_BUF =>

            Buf := Free_List;
            while Buf /= Buffers.NOBUF
              and then Requested_Buffers > Buf_List (Buf).Num_No_Jump
            loop
               Buf := Next_Data_Buf (Buf);
            end loop;

            Support.Verify
              (Buf /= Buffers.NOBUF
                and then Requested_Buffers <= Buf_List (Buf).Num_No_Jump);
      end case;

      --  Remove the allocated buffers from the free list

      Remove_From_Free_List (Buf, Requested_Buffers);

      --  Dummy initial value of Cur_Buf to avoid SPARK flow errors later on.
      --  Cur_Buf is always set by the loop that follows.

      Cur_Buf        := Buf;
      Cur_Cbuf       := To_Common_Id (Cur_Buf);

      Next_Buf       := Buf;
      Remaining_Size := Requested_Size;

      --  Allocate buffers in singly linked chain

      for Remaining in reverse Dbuf_Count range 1 .. Requested_Buffers loop
         --  Update iterators

         Cur_Buf  := Next_Buf;
         Cur_Cbuf := To_Common_Id (Cur_Buf);
         Next_Buf := Next_Data_Buf (Cur_Buf);

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

         Common.Buf_List (Cur_Cbuf).Tot_Len :=
           Remaining_Size - Common.Buf_List (Cur_Cbuf).Poffset;

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

         --  Save allocated lengths to limit later adjustments

         Common.Buf_List (Cur_Cbuf).Alloc_Len :=
           Common.Buf_List (Cur_Cbuf).Len;
         Common.Buf_List (Cur_Cbuf).Alloc_Tot_Len :=
           Common.Buf_List (Cur_Cbuf).Tot_Len;

         --  Remaining size decreases by buffer size until last buffer

         if Remaining /= 1 then
            Remaining_Size := Remaining_Size - Config.Data_Buffer_Size;
         end if;

         Buf_List (Cur_Buf).Kind := Kind;

         --  Set reference count

         Common.Buf_List (Cur_Cbuf).Ref := 1;
      end loop;

      --  Detach the allocated buffers from the free list

      Common.Buf_List (Cur_Cbuf).Next := Buffers.NOBUF;
   end Buffer_Alloc;

   -----------------
   -- Buffer_Free --
   -----------------

   procedure Buffer_Free
     (Buf      : Dbuf_Id;
      Next_Buf : out Buffers.Buffer_Id)
   with
     Refined_Global => (In_Out => (Buf_List, Common.Buf_List, Free_List))
   is
      Num : Dbuf_Count;

   begin
      Num := Buf_List (Buf).Num;

      --  Retrieve the next buffer

      Next_Buf := To_Common_Id (Buf);
      for J in Dbuf_Count range 1 .. Num loop
         Next_Buf := Common.Buf_List (Next_Buf).Next;
      end loop;

      --  Update the free list

      Insert_In_Free_List (Buf => Buf,
                           Num => Num);
   end Buffer_Free;

   ---------------------
   -- Buffer_Get_Kind --
   ---------------------

   function Buffer_Get_Kind (Buf : Dbuf_Id) return Buffers.Data_Buffer_Kind
   with
     Refined_Global => Buf_List
   is
   begin
      return Buf_List (Buf).Kind;
   end Buffer_Get_Kind;

   --------------------
   -- Buffer_Payload --
   --------------------

   function Buffer_Payload (Buf : Dbuf_Id) return System.Address with
     Refined_Global => (Common.Buf_List, Data_Array),
     SPARK_Mode => Off  --  Address attribute applied to array access
   is
      Buf_Start_Offset : constant Data_Offset :=
        Data_Offset (Buf - Dbuf_Index'First) * Config.Data_Buffer_Size;
   begin
      return Conversions.Ofs
        (Data_Array (Data_Array'First + Buf_Start_Offset)'Address,
         Integer (Common.Buf_List (To_Common_Id (Buf)).Poffset));
   end Buffer_Payload;

end AIP.Buffers.Data;
