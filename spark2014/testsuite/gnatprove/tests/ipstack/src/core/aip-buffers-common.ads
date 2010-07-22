------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management, for
--  buffers holding a reference to some external data

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
      --  Length of the data held or referenced by this buffer, which comprises
      --  the data in some buffers which follow this one for a split buffer

      Tot_Len     : Buffers.Data_Length;
      --  Total length of the data referenced by this chain of buffers

      --  For non-split buffers, the following invariant should hold:
      --  Tot_Len = Len + (if Next /= 0 then Buffers (Next).Tot_Len else 0)

      --  For split buffers, calling Last the last buffer in the split buffer,
      --  the following invariant should hold:
      --  Tot_Len = Len + (if Buffers (Last).Next /= 0 then
      --                      Buffers (Buffers (Last).Next).Tot_Len else 0)

      Ref         : AIP.U16_T;
      --  The reference count always equals the number of pointers that refer
      --  to this buffer. This can be pointers from an application or the stack
      --  itself.
   end record;

   type Buffer_Array is array (Buffers.Buffer_Index) of Buffer;

   Buf_List : Buffer_Array;

end AIP.Buffers.Common;
