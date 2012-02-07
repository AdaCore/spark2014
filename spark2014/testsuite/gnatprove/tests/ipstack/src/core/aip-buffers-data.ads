------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2012, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management, for
--  buffers holding internally some data

with AIP.Config;

--# inherit System, AIP.Config, AIP.Buffers, AIP.Buffers.Common, AIP.Support,
--#         AIP.Conversions;

private package AIP.Buffers.Data
--# own State, Free_List;
is
   pragma Preelaborate;

   --  Data buffers directly use the same type as Buffers.Buffer_Id since
   --  the same value is used to index in buffer arrays on both sides, contrary
   --  to what occurs for no-data buffers for which there is a necessary
   --  adjustment.

   type Dbuf_Id is range 0 .. Config.Data_Buffer_Num;
   Free_List : Dbuf_Id;  --  Head of the free-list for data buffers

   ---------------------------
   -- Global initialization --
   ---------------------------

   procedure Buffer_Init;
   --# global out State, Free_List;
   --  Initialize the array of buffers to zero except special fields properly
   --  given an initial value, and set the head of the free-list

   -----------------------
   -- Buffer allocation --
   -----------------------

   procedure Buffer_Alloc
     (Offset : Buffers.Buffer_Length;
      Size   : Buffers.Data_Length;
      Kind   : Buffers.Data_Buffer_Kind;
      Buf    : out Dbuf_Id);
   --# global in out Common.Buf_List, State, Free_List;

   --------------------------------------------
   -- Buffer struct accessors and operations --
   --------------------------------------------

   function Buffer_Payload (Buf : Dbuf_Id) return System.Address;
   --# global in State;

   function Buffer_Get_Kind (Buf : Dbuf_Id) return Buffers.Data_Buffer_Kind;
   --# global in State;

   procedure Buffer_Link (Buf : Dbuf_Id; Next : Dbuf_Id);
   --# global in out State;
   --  Link buffer Buf to buffer Next

   ----------------------------
   -- Buffer id translations --
   ----------------------------

   function To_Dbuf_Id (Buf : Buffers.Buffer_Id) return Dbuf_Id;
   function To_Common_Id (Buf : Dbuf_Id) return Buffers.Buffer_Id;

   pragma Inline (To_Common_Id);
   pragma Inline (To_Dbuf_Id);

end AIP.Buffers.Data;
