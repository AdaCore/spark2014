------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management, for
--  buffers holding a reference to some external data

with AIP.Config;

--# inherit System, AIP.Config, AIP.Support, AIP.Buffers, AIP.Buffers.Common,
--#         AIP.Conversions;

private package AIP.Buffers.No_Data
--# own State, Free_List;
is
   pragma Preelaborate;

   --  Redefine type U16_T locally so that No_Data.Buffer_Id is of a different
   --  type from Buffers.Buffer_Id. This ensures that the proper conversion is
   --  always performed from a No_Data.Buffer_Id to a Buffers.Buffer_Id and
   --  vice-versa.
   type U16_T is range AIP.U16_T'First .. AIP.U16_T'Last;

   Buffer_Num : constant U16_T := U16_T (Config.No_Data_Buffer_Num);

   subtype Buffer_Id is U16_T range 0 .. Buffer_Num;

   NOBUF : constant Buffer_Id := 0;

   Free_List : Buffer_Id;  --  Head of the free-list for no-data buffers

   ---------------------------
   -- Buffer Id adjustments --
   ---------------------------

   --  To map indices in common array to local ones for ref buffer
   --  specific structures and vice-versa.

   function To_Ref_Id (Buf : Buffers.Buffer_Id) return Buffer_Id;
   function To_Common_Id (Buf : Buffer_Id) return Buffers.Buffer_Id;

   ---------------------------
   -- Global initialization --
   ---------------------------

   procedure Buffer_Init;
   --# global out State, Free_List;
   --  Initialize the array of buffers to zero and set the head of
   --  the free-list

   -----------------------
   -- Buffer allocation --
   -----------------------

   procedure Buffer_Alloc
     (Offset   : Buffers.Buffer_Length;
      Size     : Buffers.Data_Length;
      Data_Ref : System.Address;
      Buf      : out Buffer_Id);
   --# global in out Common.Buf_List, State, Free_List;

   --------------------------------------------
   -- Buffer struct accessors and operations --
   --------------------------------------------

   function Buffer_Payload (Buf : Buffer_Id) return System.Address;
   --# global in State;

end AIP.Buffers.No_Data;
