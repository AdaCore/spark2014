------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management, for
--  buffers holding internally some data

--# inherit AIP.Buffers, AIP.Buffers.Common, AIP.Support, AIP.Conversions;

private package AIP.Buffers.Data
--# own State, Free_List;
is
   --  Data buffers directly use the same type as Buffers.Buffer_Id since
   --  the same value is used to index in buffer arrays on both sides, contrary
   --  to what occurs for no-data buffers for which there is a necessary
   --  adjustment.

   Buffer_Num : constant AIP.U16_T := Buffers.Data_Buffer_Num;

   subtype Buffer_Id is AIP.U16_T range 0 .. Buffer_Num;

   Free_List : Buffer_Id;  --  Head of the free-list for data buffers

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
     (Offset :     Buffers.Buffer_Length;
      Size   :     Buffers.Data_Length;
      Kind   :     Buffers.Data_Buffer_Kind;
      Buf    : out Buffer_Id);
   --# global in out Common.Buf_List, State, Free_List;
   --  Allocate and return a new Buf of kind Kind, aimed at holding Size
   --  elements of data starting at offset Offset

   -----------------------------
   -- Buffer struct accessors --
   -----------------------------

   function Buffer_Payload (Buf : Buffer_Id) return AIP.IPTR_T;
   --# global in State;
   --  Pointer to data held by buffer Buf

   ----------------------------------
   -- Buffer reference and release --
   ----------------------------------

   procedure Buffer_Link (Buf : Buffer_Id; Next : Buffer_Id);
   --# global in out State;
   --  Link buffer Buf to buffer Next

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

end AIP.Buffers.Data;
