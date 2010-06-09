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
   type Buffer is record
      --  Next buffer in singly linked chain
      Next    : Buffers.Buffer_Id;

      --  Length of the data held or referenced by this buffer
      Len     : Buffers.Data_Length;

      --  Total length of the data referenced by this chain of buffers
      --
      --  The following invariant should hold:
      --  Tot_Len = Len + (if Next /= 0 then Buffers (Next).Tot_Len else 0)
      Tot_Len : Buffers.Data_Length;

      --  The reference count always equals the number of pointers that refer
      --  to this buffer. This can be pointers from an application or the stack
      --  itself.
      Ref     : AIP.U16_T;
   end record;

   type Buffer_Array is array (Buffers.Buffer_Index) of Buffer;

   Buf_List : Buffer_Array;

end AIP.Buffers.Common;
