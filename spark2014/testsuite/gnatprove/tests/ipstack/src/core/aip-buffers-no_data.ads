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
   Buffer_Num : constant Positive := Buffers.Ref_Num;

   subtype Buffer_Id is Natural range 0 .. Buffer_Num;

   -----------------------
   -- Buffer allocation --
   -----------------------

   procedure Buffer_Alloc
     (Size   :     Buffers.Data_Length;
      Buf    : out Buffer_Id);
   --# global in out State;
   --  Allocate and return a new Buf of kind Kind, aimed at referending Size
   --  elements of data

end AIP.Buffers.No_Data;
