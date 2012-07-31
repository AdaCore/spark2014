------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2012, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management, for
--  buffers holding internally some data

with AIP.Config;

--# inherit System, AIP.Config, AIP.Buffers, AIP.Buffers.Common, AIP.Support,
--#         AIP.Conversions;

private package AIP.Buffers.Data
--# own State, Free_List;
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

   Free_List : Dbuf_Id;  --  Head of the free-list for data buffers

   ---------------------------
   -- Global initialization --
   ---------------------------

   procedure Buffer_Init;
   --# global out State, Free_List;
   --  Initialize the array of buffers to zero except special fields properly
   --  given an initial value, and set the head of the free-list

   -----------------------
   -- Buffer allocation --
   -----------------------

   procedure Buffer_Alloc
     (Offset : Buffers.Buffer_Length;
      Size   : Buffers.Data_Length;
      Kind   : Buffers.Data_Buffer_Kind;
      Buf    : out Dbuf_Id);
   --# global in out Common.Buf_List, State, Free_List;

   procedure Buffer_Free
     (Buf      : Dbuf_Id;
      Next_Buf : out Buffers.Buffer_Id);
   --# global in out Common.Buf_List, State, Free_List;
   --  Free buffer Buf, and set the next buffer

   --------------------------------------------
   -- Buffer struct accessors and operations --
   --------------------------------------------

   function Buffer_Payload (Buf : Dbuf_Id) return System.Address;
   --# global in State;

   function Buffer_Get_Kind (Buf : Dbuf_Id) return Buffers.Data_Buffer_Kind;
   --# global in State;

   procedure Buffer_Link
     (Buf      :     Dbuf_Id;
      Next     :     Dbuf_Id;
      Last_Buf : out Buffers.Buffer_Id;
      Num      : out AIP.U8_T);
   --# global in     Common.Buf_List;
   --#        in out State;
   --  Link buffer Buf to buffer Next. Return the last buffer in the linked
   --  list starting at Buf, so that the caller can update the global Next
   --  link. Also return the number Num of buffers that have been prepended to
   --  Next.

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

   function Next_Data_Buf (Buf : Dbuf_Id) return Dbuf_Id;
   --# global in Common.Buf_List;
   --  Return next buffer, performing necessary conversions between Dbuf_Id and
   --  Buffers.Buffer_Id.

   procedure Advance_To_Next_Contiguous_Block
     (Buf      : in out Dbuf_Id;
      Prev_Buf : out Dbuf_Id;
      Num      : out Dbuf_Count);
   --# global in Common.Buf_List, State;
   --  Set Buf to the first buffer of the contiguous block that follows it,
   --  Prev_Buf to the last buffer before it, and Num to the number of buffers
   --  from the previous value of Buf to Prev_Buf (included).

   procedure Insert_Contiguous_In_Free_List (Buf : Dbuf_Id; Num : Dbuf_Count);
   --# global in out Common.Buf_List, State, Free_List;
   --  Insert Num contiguous buffers in the free list, starting with buffer
   --  Buf, in a way that preserves the ordering and structure of the free
   --  list.

   procedure Insert_In_Free_List (Buf : Dbuf_Id; Num : Dbuf_Count);
   --# global in out Common.Buf_List, State, Free_List;
   --  Insert Num buffers in the free list, starting with buffer Buf, in a
   --  way that preserves the ordering and structure of the free list. The
   --  Num buffers may not be contiguous.

   procedure Remove_From_Free_List (Buf : Dbuf_Id; Num : Dbuf_Count);
   --# global in out Common.Buf_List, State, Free_List;
   --  Remove Num buffers from the free list, starting with buffer Buf, which
   --  should be the first one in a sequence of contiguous buffers. Note that
   --  the Num buffers starting from Buf may not be contiguous. It is the
   --  responsibility of the caller to ensure that this sequence of buffers is
   --  appropriate.

end AIP.Buffers.Data;
