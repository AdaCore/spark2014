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

   function Buffer_Len (Buf : Buffer_Id) return AIP.U16_T;
   --# global in State;
   --  Amount of packet data held in the first chunk of buffer Buf

end AIP.Buffers.No_Data;
