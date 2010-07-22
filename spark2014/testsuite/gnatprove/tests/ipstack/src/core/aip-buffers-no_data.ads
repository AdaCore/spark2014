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

   -----------------------
   -- Buffer adjustment --
   -----------------------

   function Adjust_Id (Buf : Buffers.Buffer_Id) return Buffer_Id;

   function Adjust_Back_Id (Buf : Buffer_Id) return Buffers.Buffer_Id;

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
     (Size   :     Buffers.Data_Length;
      Buf    : out Buffer_Id);
   --# global in out Common.Buf_List, State, Free_List;
   --  Allocate and return a new Buf of kind Kind, aimed at referending Size
   --  elements of data

   -----------------------------
   -- Buffer struct accessors --
   -----------------------------

   function Buffer_Payload (Buf : Buffer_Id) return System.Address;
   --# global in State;
   --  Pointer to data referenced by buffer Buf

   -----------------------
   -- Buffer operations --
   -----------------------

   procedure Buffer_Header
     (Buf  : Buffer_Id;
      Bump : AIP.S16_T;
      Err  : in out AIP.Err_T);
   --# global in out State;
   --  Move the payload pointer of Buf by Bump elements, signed.
   --  Typically used to reveal or hide protocol headers.

end AIP.Buffers.No_Data;
