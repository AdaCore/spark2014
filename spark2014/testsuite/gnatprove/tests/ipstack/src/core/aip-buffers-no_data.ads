------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management, for
--  buffers holding a reference to some external data

with AIP.Config;
limited with AIP.Buffers.Common;

private package AIP.Buffers.No_Data with
   Abstract_State => (State with Part_Of => AIP.Buffers.State)
is
   pragma Preelaborate;

   type Rbuf_Id is range 0 .. Config.No_Data_Buffer_Num;
   Free_List : Rbuf_Id  --  Head of the free-list for no-data buffers
     with Part_Of => AIP.Buffers.State;

   ---------------------------
   -- Global initialization --
   ---------------------------

   procedure Buffer_Init
   --  Initialize the array of buffers to zero and set the head of
   --  the free-list
   with
     Global => (Output => (Free_List, State));

   -----------------------
   -- Buffer allocation --
   -----------------------

   procedure Buffer_Alloc
     (Offset   : Buffers.Buffer_Length;
      Size     : Buffers.Data_Length;
      Data_Ref : System.Address;
      Buf      : out Rbuf_Id)
   with
     Global => (In_Out => (Common.Buf_List, Free_List, State));

   procedure Buffer_Free
     (Buf      : Rbuf_Id;
      Next_Buf : out Buffers.Buffer_Id)
   --  Free buffer Buf, and set the next buffer
   with
     Global => (In_Out => (Common.Buf_List, Free_List));

   --------------------------------------------
   -- Buffer struct accessors and operations --
   --------------------------------------------

   function Buffer_Payload (Buf : Rbuf_Id) return System.Address with
     Global => (Common.Buf_List, State);

   --------------------------------------------
   -- Common/specific buffer Id translations --
   --------------------------------------------

   function To_Rbuf_Id (Buf : Buffers.Buffer_Id) return Rbuf_Id;
   function To_Common_Id (Buf : Rbuf_Id) return Buffers.Buffer_Id;

end AIP.Buffers.No_Data;
