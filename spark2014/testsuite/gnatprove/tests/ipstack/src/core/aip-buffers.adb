------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Buffers.Data;
with AIP.Buffers.No_Data;

package body AIP.Buffers
--# own State is AIP.Buffers.Data.State, AIP.Buffers.No_Data.State;
is
   --------------------
   -- Is_Data_Buffer --
   --------------------

   function Is_Data_Buffer (Buf : Buffer_Id) return Boolean is
   begin
      return Buf <= Chunk_Num;
   end Is_Data_Buffer;

   -----------------------
   -- Adjust_No_Data_Id --
   -----------------------

   function Adjust_No_Data_Id (Buf : Buffer_Id) return No_Data.Buffer_Id is
   begin
      return No_Data.U16_T (Buf - Chunk_Num);
   end Adjust_No_Data_Id;

   ----------------------------
   -- Adjust_Back_No_Data_Id --
   ----------------------------

   function Adjust_Back_No_Data_Id (Buf : No_Data.Buffer_Id) return Buffer_Id
   is
   begin
      return AIP.U16_T (Buf) + Chunk_Num;
   end Adjust_Back_No_Data_Id;

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Offset :     Offset_Length;
      Size   :     Data_Length;
      Kind   :     Buffer_Kind;
      Buf    : out Buffer_Id)
   --# global in out Data.State, No_Data.State;
   is
      No_Data_Buf : No_Data.Buffer_Id;
   begin
      if Kind in Data_Buffer_Kind then
         Data.Buffer_Alloc (Offset => Offset,
                            Size   => Size,
                            Kind   => Kind,
                            Buf    => Buf);
      else
         No_Data.Buffer_Alloc (Size => Size,
                               Buf  => No_Data_Buf);
         Buf := Adjust_Back_No_Data_Id (No_Data_Buf);
      end if;
   end Buffer_Alloc;

   ----------------
   -- Buffer_Len --
   ----------------

   function Buffer_Len (Buf : Buffer_Id) return AIP.U16_T
   --# global in Data.State, No_Data.State;
   is
      Result : AIP.U16_T;
   begin
      if Is_Data_Buffer (Buf) then
         Result := Data.Buffer_Len (Buf);
      else
         Result := No_Data.Buffer_Len (Adjust_No_Data_Id (Buf));
      end if;
      return Result;
   end Buffer_Len;

end AIP.Buffers;
