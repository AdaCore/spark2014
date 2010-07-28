------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Buffers.Common;
with AIP.Conversions;
with AIP.Support;

package body AIP.Buffers.No_Data
--# own State is Buf_List;
is

   subtype Buffer_Index is U16_T range 1 .. Buffer_Num;

   type Buffer is record
      Data_Ref : System.Address;
      --  Reference to the start of buffer data
   end record;

   type Buffer_Array is array (Buffer_Index) of Buffer;
   Buf_List : Buffer_Array;

   ---------------
   -- To_Ref_Id --
   ---------------

   function To_Ref_Id (Buf : Buffers.Buffer_Id) return Buffer_Id
   is
      Result : Buffer_Id;
   begin
      if Buf = Buffers.NOBUF then
         Result := NOBUF;
      else
         Result := U16_T (Buf - Config.Data_Buffer_Num);
      end if;
      return Result;
   end To_Ref_Id;

   ------------------
   -- To_Common_Id --
   ------------------

   function To_Common_Id (Buf : Buffer_Id) return Buffers.Buffer_Id
   is
      Result : Buffers.Buffer_Id;
   begin
      if Buf = NOBUF then
         Result := Buffers.NOBUF;
      else
         Result := AIP.U16_T (Buf) + Config.Data_Buffer_Num;
      end if;
      return Result;
   end To_Common_Id;

   -----------------
   -- Buffer_Init --
   -----------------

   procedure Buffer_Init
   --# global out Buf_List, Free_List;
   is
   begin
      --  Initialize all the memory for buffers to zero and point the head
      --  of the free-list to the first buffer

      Buf_List := Buffer_Array'
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
      Buf      : out Buffer_Id)
   --# global in out Common.Buf_List, Buf_List, Free_List;
   is
      Cbuf : Buffers.Buffer_Id;
   begin
      --  Check that the free-list is not empty and pop the head

      Support.Verify (Free_List /= NOBUF);

      Buf       := Free_List;
      Cbuf      := To_Common_Id (Buf);
      Free_List := To_Ref_Id (Common.Buf_List (Cbuf).Next);

      --  Set common fields and reference count, then specific fields

      Common.Buf_List (Cbuf).Next    := Buffers.NOBUF;
      Common.Buf_List (Cbuf).Len     := Size;
      Common.Buf_List (Cbuf).Tot_Len := Size;
      Common.Buf_List (Cbuf).Poffset := Offset;
      Common.Buf_List (Cbuf).Ref     := 1;

      Buf_List (Buf).Data_Ref := Data_Ref;
   end Buffer_Alloc;

   --------------------
   -- Buffer_Payload --
   --------------------

   function Buffer_Payload (Buf : Buffer_Id) return System.Address
   --# global in Buf_List;
   is
   begin
      return Conversions.Ofs
        (Buf_List (Buf).Data_Ref,
         Integer (Common.Buf_List (To_Common_Id (Buf)).Poffset));
   end Buffer_Payload;

end AIP.Buffers.No_Data;
