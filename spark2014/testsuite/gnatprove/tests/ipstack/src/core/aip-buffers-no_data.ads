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

   type Rbuf_Id is range 0 .. Config.No_Data_Buffer_Num;
   Free_List : Rbuf_Id;  --  Head of the free-list for no-data buffers

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
      Buf      : out Rbuf_Id);
   --# global in out Common.Buf_List, State, Free_List;

   --------------------------------------------
   -- Buffer struct accessors and operations --
   --------------------------------------------

   function Buffer_Payload (Buf : Rbuf_Id) return System.Address;
   --# global in Common.Buf_List, State;

   --------------------------------------------
   -- Common/specific buffer Id translations --
   --------------------------------------------

   function To_Rbuf_Id (Buf : Buffers.Buffer_Id) return Rbuf_Id;
   function To_Common_Id (Buf : Rbuf_Id) return Buffers.Buffer_Id;

end AIP.Buffers.No_Data;
