------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Support;
with AIP.Buffers.Common;

package body AIP.Buffers.No_Data
--# own State is Buf_List;
is
   subtype Buffer_Index is U16_T range 1 .. Buffer_Num;

   type Buffer is record
      --  Reference to the actual data
      Payload_Ref : AIP.IPTR_T;
   end record;

   type Buffer_Array is array (Buffer_Index) of Buffer;

   Buf_List : Buffer_Array;

   ---------------
   -- Adjust_Id --
   ---------------

   function Adjust_Id (Buf : Buffers.Buffer_Id) return Buffer_Id
   is
      Result : Buffer_Id;
   begin
      if Buf = Buffers.NOBUF then
         Result := NOBUF;
      else
         Result := U16_T (Buf - Buffers.Chunk_Num);
      end if;
      return Result;
   end Adjust_Id;

   --------------------
   -- Adjust_Back_Id --
   --------------------

   function Adjust_Back_Id (Buf : Buffer_Id) return Buffers.Buffer_Id
   is
      Result : Buffers.Buffer_Id;
   begin
      if Buf = NOBUF then
         Result := Buffers.NOBUF;
      else
         Result := AIP.U16_T (Buf) + Buffers.Chunk_Num;
      end if;
      return Result;
   end Adjust_Back_Id;

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Size   :     Buffers.Data_Length;
      Buf    : out Buffer_Id)
   --# global in out Common.Buf_List, Buf_List, Free_List;
   is
      Adjusted_Buf : Buffers.Buffer_Id;
   begin
      --  Check that the free-list is not empty
      Support.Verify (Free_List /= NOBUF);

      --  Pop the head of the free-list
      Buf                                    := Free_List;
      Adjusted_Buf                           := Adjust_Back_Id (Buf);
      Free_List                              :=
        Adjust_Id (Common.Buf_List (Adjusted_Buf).Next);

      --  Set common fields

      -- accept W, 169, AIP.Buffers.Common.Buf_List,
      --           "Direct update of own variable of a non-enclosing package";
      Common.Buf_List (Adjusted_Buf).Next    := Buffers.NOBUF;
      -- end accept;
      Common.Buf_List (Adjusted_Buf).Len     := Size;
      Common.Buf_List (Adjusted_Buf).Tot_Len := Size;
      --  Set reference count
      Common.Buf_List (Adjusted_Buf).Ref     := 1;

      --  Set specific fields

      --  Caller must set this field properly, afterwards
      Buf_List (Buf).Payload_Ref             := AIP.NULIPTR;
   end Buffer_Alloc;

   --------------------
   -- Buffer_Payload --
   --------------------

   function Buffer_Payload (Buf : Buffer_Id) return AIP.IPTR_T
   --# global in Buf_List;
   is
   begin
      return Buf_List (Buf).Payload_Ref;
   end Buffer_Payload;

end AIP.Buffers.No_Data;
