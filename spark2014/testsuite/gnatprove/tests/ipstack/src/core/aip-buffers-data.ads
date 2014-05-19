------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management, for
--  buffers holding internally some data

with AIP.Config;
limited with AIP.Buffers.Common;

private package AIP.Buffers.Data with
   Abstract_State => (State with Part_Of => AIP.Buffers.State)
is
   pragma Preelaborate;

   --  Data buffers directly use the same type as Buffers.Buffer_Id since
   --  the same value is used to index in buffer arrays on both sides, contrary
   --  to what occurs for no-data buffers for which there is a necessary
   --  adjustment.

   type Dbuf_Id is range 0 .. Config.Data_Buffer_Num;

   --  The free list is an ordered sequence of buffers, so that the buffers
   --  with the least contiguous space (counting the available buffers that
   --  follow directly a buffer) come first.
   --
   --  - When allocating a LINK_BUF buffer (whose memory can be
   --  non-contiguous), we use buffers in the order in which they appear in
   --  the free list.
   --
   --  - When allocating a SPLIT_BUF buffer (whose memory should be
   --  contiguous), we use the first contiguous chain of buffers in the free
   --  list that contain enough memory. We possibly reorder the free list to
   --  maintain the ordering property.
   --
   --  - When freeing a buffer, we look at the free list to see if the
   --  preceding and/or following buffers are already in the free list, and we
   --  insert appropriately the freed buffers in the free list to maintain the
   --  ordering property.

   Free_List : Dbuf_Id with  --  Head of the free-list for data buffers
     Part_Of => AIP.Buffers.State;

   ---------------------------
   -- Global initialization --
   ---------------------------

   procedure Buffer_Init
   --  Initialize the array of buffers to zero except special fields properly
   --  given an initial value, and set the head of the free-list
   with
     Global => (Output => (Free_List, State));

   -----------------------
   -- Buffer allocation --
   -----------------------

   procedure Buffer_Alloc
     (Offset : Buffers.Buffer_Length;
      Size   : Buffers.Data_Length;
      Kind   : Buffers.Data_Buffer_Kind;
      Buf    : out Dbuf_Id)
   with
     Global => (In_Out => (Common.Buf_List, Free_List, State));

   procedure Buffer_Free
     (Buf      : Dbuf_Id;
      Next_Buf : out Buffers.Buffer_Id)
   --  Free buffer Buf, and set the next buffer
   with
     Global => (In_Out => (Common.Buf_List, Free_List, State));

   --------------------------------------------
   -- Buffer struct accessors and operations --
   --------------------------------------------

   function Buffer_Payload (Buf : Dbuf_Id) return System.Address with
     Global => (Common.Buf_List, State);

   function Buffer_Get_Kind (Buf : Dbuf_Id) return Buffers.Data_Buffer_Kind
   with
     Global => State;

   ----------------------------
   -- Buffer id translations --
   ----------------------------

   function To_Dbuf_Id (Buf : Buffers.Buffer_Id) return Dbuf_Id;
   function To_Common_Id (Buf : Dbuf_Id) return Buffers.Buffer_Id;

   pragma Inline (To_Common_Id);
   pragma Inline (To_Dbuf_Id);

private

   --  SPARK requires that subprograms defined in a package body only have no
   --  separate declaration. The style checks used here require that there is
   --  always a separate declaration for a subprogram. We comply with both by
   --  declaring these internal subprograms in the private part of the package
   --  spec. This also requires that some subtypes are defined in this private
   --  part.

   subtype Dbuf_Index is Dbuf_Id range 1 .. Dbuf_Id'Last;
   subtype Dbuf_Count_Or_Null is Dbuf_Id;
   subtype Dbuf_Count is Dbuf_Index;

   function Next_Data_Buf (Buf : Dbuf_Id) return Dbuf_Id
   --  Return next buffer, performing necessary conversions between Dbuf_Id and
   --  Buffers.Buffer_Id.
   with
     Global => Common.Buf_List;

   procedure Advance_To_Next_Contiguous_Block
     (Buf      : in out Dbuf_Id;
      Prev_Buf : out Dbuf_Id;
      Num      : out Dbuf_Count)
   --  Set Buf to the first buffer of the contiguous block that follows it,
   --  Prev_Buf to the last buffer before it, and Num to the number of buffers
   --  from the previous value of Buf to Prev_Buf (included).
   with
    Global => (Input => (Common.Buf_List, State));

   procedure Insert_Contiguous_In_Free_List (Buf : Dbuf_Id; Num : Dbuf_Count)
   --  Insert Num contiguous buffers in the free list, starting with buffer
   --  Buf, in a way that preserves the ordering and structure of the free
   --  list. Inserting those contiguous buffers should not lead to fragmenting
   --  the free list, which depends on the caller knowing that the buffers
   --  inserted do not follow or precede other buffers already in the free
   --  list.
   with
     Global => (In_Out => (Common.Buf_List, Free_List, State));

   procedure Remove_From_Free_List (Buf : Dbuf_Id; Num : Dbuf_Count)
   --  Remove Num buffers from the free list, starting with buffer Buf, which
   --  should be the first one in a sequence of contiguous buffers. Note that
   --  the Num buffers starting from Buf may not be contiguous. It is the
   --  responsibility of the caller to ensure that this sequence of buffers is
   --  appropriate.
   with
     Global => (In_Out => (Common.Buf_List, Free_List, State));

   procedure Extract_Contiguous_From_Free_List
     (Buf : in out Dbuf_Id;
      Num : in out Dbuf_Count)
   --  Prepare for the insertion of Num contiguous buffers starting at Buf in
   --  the free list, by removing from the free list those buffers preceding
   --  and following this contiguous block. Return in Buf and Num the possibly
   --  larger contiguous block formed by coalescing all these buffers in a
   --  single chain. Note that this new contiguous block can now be inserted in
   --  the free list by calling Insert_Contiguous_In_Free_List without
   --  introducing fragmentation.
   with
     Global => (In_Out => (Common.Buf_List, Free_List, State));

   procedure Insert_In_Free_List (Buf : Dbuf_Id; Num : Dbuf_Count)
   --  Insert Num buffers in the free list, starting with buffer Buf, in a
   --  way that preserves the ordering and structure of the free list. The
   --  Num buffers may not be contiguous.
   with
     Global => (In_Out => (Common.Buf_List, Free_List, State));

end AIP.Buffers.Data;
