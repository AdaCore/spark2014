------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with AIP.Buffers.Common;
with AIP.Conversions;
with AIP.Support;

package body AIP.Buffers.No_Data with
  Refined_State => (State => Buf_List)
is

   type Buffer is record
      Data_Ref : System.Address;
      --  Reference to the start of buffer data
   end record;

   subtype Rbuf_Index is Rbuf_Id range 1 .. Rbuf_Id'Last;
   type Rbuf_Array is array (Rbuf_Index) of Buffer;
   Buf_List : Rbuf_Array;

   ----------------
   -- To_Rbuf_Id --
   ----------------

   function To_Rbuf_Id
     (Buf : Buffers.Buffer_Id) return Rbuf_Id
   is
      Result : Rbuf_Id;
   begin
      if Buf = Buffers.NOBUF then
         Result := Buffers.NOBUF;
      else
         Result := Rbuf_Id (Buf - Config.Data_Buffer_Num);
      end if;
      return Result;
   end To_Rbuf_Id;

   ------------------
   -- To_Common_Id --
   ------------------

   function To_Common_Id
     (Buf : Rbuf_Id) return Buffers.Buffer_Id
   is
      Result : Buffers.Buffer_Id;
   begin
      if Buf = Buffers.NOBUF then
         Result := Buffers.NOBUF;
      else
         Result := Buffers.Buffer_Id (Buf) + Config.Data_Buffer_Num;
      end if;
      return Result;
   end To_Common_Id;

   -----------------
   -- Buffer_Init --
   -----------------

   procedure Buffer_Init with
     Refined_Global => (Output => (Buf_List, Free_List))
   is
   begin
      --  Initialize all the memory for buffers to zero and point the head
      --  of the free-list to the first buffer

      Buf_List := Rbuf_Array'
        (others => Buffer'(Data_Ref => System.Null_Address));
      Free_List := Buf_List'First;
   end Buffer_Init;

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Offset   : Buffers.Buffer_Length;
      Size     : Buffers.Data_Length;
      Data_Ref : System.Address;
      Buf      : out Rbuf_Id)
   with
     Refined_Global => (In_Out => (Buf_List, Common.Buf_List, Free_List))
   is
      Cbuf : Buffers.Buffer_Id;
   begin
      --  Check that the free-list is not empty and pop the head

      Support.Verify (Free_List /= Buffers.NOBUF);

      Buf       := Free_List;
      Cbuf      := To_Common_Id (Buf);
      Free_List := To_Rbuf_Id (Common.Buf_List (Cbuf).Next);

      --  Set common fields and reference count, then specific fields

      Common.Buf_List (Cbuf).Next          := Buffers.NOBUF;
      Common.Buf_List (Cbuf).Len           := Size;
      Common.Buf_List (Cbuf).Tot_Len       := Size;
      Common.Buf_List (Cbuf).Alloc_Len     := Size;
      Common.Buf_List (Cbuf).Alloc_Tot_Len := Size;
      Common.Buf_List (Cbuf).Poffset       := Offset;
      Common.Buf_List (Cbuf).Ref           := 1;

      Buf_List (Buf).Data_Ref := Data_Ref;
   end Buffer_Alloc;

   -----------------
   -- Buffer_Free --
   -----------------

   procedure Buffer_Free
     (Buf      : Rbuf_Id;
      Next_Buf : out Buffers.Buffer_Id)
   is
      Cbuf : Buffers.Buffer_Id;

   begin
      Cbuf := To_Common_Id (Buf);

      --  Retrieve the next buffer

      Next_Buf := Common.Buf_List (Cbuf).Next;

      --  Update the free list

      Common.Buf_List (Cbuf).Next := To_Common_Id (Free_List);
      Free_List := Buf;
   end Buffer_Free;

   --------------------
   -- Buffer_Payload --
   --------------------

   function Buffer_Payload (Buf : Rbuf_Id) return System.Address with
     Refined_Global => (Buf_List, Common.Buf_List)
   is
   begin
      return Conversions.Ofs
        (Buf_List (Buf).Data_Ref,
         Integer (Common.Buf_List (To_Common_Id (Buf)).Poffset));
   end Buffer_Payload;

end AIP.Buffers.No_Data;
