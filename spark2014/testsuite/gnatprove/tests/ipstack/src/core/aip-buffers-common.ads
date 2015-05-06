------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management.
--  Common data structures for both Data and No_Data buffers.

private package AIP.Buffers.Common is
   pragma Preelaborate;

   type Packet_Queue_Ptrs is array (Buffers.Packet_Layer) of Buffers.Buffer_Id;

   type Buffer is record
      Next        : Buffers.Buffer_Id;
      --  Next buffer in this buffer chain

      Next_Packet : Packet_Queue_Ptrs;
      --  Next packet in queue

      Packet_Info : System.Address;
      --  Information associated to this buffer by the layer 3 (transport)
      --  protocol.

      Len         : Buffers.Data_Length;
      --  Length of the payload data held or referenced by this buffer, which
      --  comprises the data in some buffers which follow this one for a split
      --  buffer.

      Tot_Len     : Buffers.Data_Length;
      --  Total length of the payload data referenced by this chain of buffers

      --  For non-split buffers, the following invariant should hold:
      --  Tot_Len = Len + (if Next /= 0 then Buffers (Next).Tot_Len else 0)

      --  For split buffers, calling Last the last buffer in the split buffer,
      --  the following invariant should hold:
      --  Tot_Len = Len + (if Buffers (Last).Next /= 0 then
      --                      Buffers (Buffers (Last).Next).Tot_Len else 0)

      Alloc_Len     : Buffers.Data_Length;
      Alloc_Tot_Len : Buffers.Data_Length;
      --  Initial value of Len and Tot_Len at buffer allocation time.
      --  Used to control later adjustments of Len and Tot_Len.

      Poffset     : Buffers.Buffer_Length;
      --  Offset to payload from start of data block

      Ref         : AIP.U16_T;
      --  The reference count always equals the number of pointers that refer
      --  to this buffer. This can be pointers from an application or the stack
      --  itself.

   end record;

   subtype Buffer_Index is AIP.U16_T range 1 .. Buffers.Buffer_Id'Last;
   type Buffer_Array is array (Buffer_Index) of Buffer;
   Buf_List : Buffer_Array with Part_Of => AIP.Buffers.State;

   function Is_Data_Buffer (Buf : Buffers.Buffer_Id) return Boolean;
   --  Return True if Buf is a Data buffer, False if it is a No_Data buffer

end AIP.Buffers.Common;
