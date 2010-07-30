------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management.
--  Common data structures for both Data and No_Data buffers.

--# inherit AIP.Buffers;

private package AIP.Buffers.Common
--# own Buf_List;
is
   pragma Preelaborate;

   type Buffer is record
      Next        : Buffers.Buffer_Id;
      --  Next buffer in this buffer chain

      Next_Packet : Buffers.Buffer_Id;
      --  Next packet in queue

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

      Poffset     : Buffers.Buffer_Length;
      --  Offset to payload from start of data block

      Ref         : AIP.U16_T;
      --  The reference count always equals the number of pointers that refer
      --  to this buffer. This can be pointers from an application or the stack
      --  itself.
   end record;

   subtype Buffer_Index is AIP.U16_T range 1 .. Buffers.Buffer_Id'Last;
   type Buffer_Array is array (Buffer_Index) of Buffer;
   Buf_List : Buffer_Array;

end AIP.Buffers.Common;
