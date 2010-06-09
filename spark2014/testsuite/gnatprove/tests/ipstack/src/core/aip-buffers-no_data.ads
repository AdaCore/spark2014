------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management, for
--  buffers holding a reference to some external data

--# inherit AIP.Buffers, AIP.Support;

private package AIP.Buffers.No_Data
--# own State;
is
   --  Redefine type U16_T locally so that No_Data.Buffer_Id is of a different
   --  type from Buffers.Buffer_Id. This ensures that the proper conversion is
   --  always performed from a No_Data.Buffer_Id to a Buffers.Buffer_Id and
   --  vice-versa.
   type U16_T is range AIP.U16_T'First .. AIP.U16_T'Last;

   Buffer_Num : constant U16_T := U16_T (Buffers.Ref_Num);

   subtype Buffer_Id is U16_T range 0 .. Buffer_Num;

   NOBUF : constant Buffer_Id := 0;

   -----------------------
   -- Buffer allocation --
   -----------------------

   procedure Buffer_Alloc
     (Size   :     Buffers.Data_Length;
      Buf    : out Buffer_Id);
   --# global in out State;
   --  Allocate and return a new Buf of kind Kind, aimed at referending Size
   --  elements of data

   -----------------------------
   -- Buffer struct accessors --
   -----------------------------

   function Buffer_Tlen (Buf : Buffer_Id) return AIP.U16_T;
   --# global in State;
   --  Amount of packet data referenced by buffer Buf

   function Buffer_Payload (Buf : Buffer_Id) return AIP.IPTR_T;
   --# global in State;
   --  Pointer to data referenced by buffer Buf

   ----------------------------------
   -- Buffer reference and release --
   ----------------------------------

   procedure Buffer_Ref (Buf : Buffer_Id);
   --# global in out State;
   --  Increase reference count of Buffer Buf, with influence on Buffer_Free

   procedure Buffer_Free (Buf : Buffer_Id; Dealloc : out Boolean);
   --# global in out State;
   --  Decrement Buf's reference count, and deallocate if the count reaches
   --  zero. Return whether the buffer was de-allocated.

end AIP.Buffers.No_Data;
