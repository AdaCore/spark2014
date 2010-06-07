------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Buffers.Data;
with AIP.Buffers.No_Data;

package body AIP.Buffers
--# own State is Data.State, No_Data.State;
is
   ---------------
   -- Adjust_Id --
   ---------------

   function Adjust_Id (Buf : Buffer_Id) return Buffer_Id is
      Adjusted_Buf : Buffer_Id;
   begin
      if Buf > Chunk_Num then
         --  Buffer without data: Kind = REF_BUF
         Adjusted_Buf := Buf - Chunk_Num;
      else
         --  Buffer with data: Kind = MONO_BUF or Kind = LINK_BUF
         Adjusted_Buf := Buf;
      end if;
      return Adjusted_Buf;
   end Adjust_Id;

   ----------------------------
   -- Adjust_Back_No_Data_Id --
   ----------------------------

   function Adjust_Back_No_Data_Id (Buf : Buffer_Id) return Buffer_Id is
   begin
      return Buf + Chunk_Num;
   end Adjust_Back_No_Data_Id;

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Offset :     Offset_Length;
      Size   :     Data_Length;
      Kind   :     Buffer_Kind;
      Buf    : out Buffer_Id)
   is
   begin
      if Kind in Data_Buffer_Kind then
         Data.Buffer_Alloc (Offset => Offset,
                            Size   => Size,
                            Kind   => Kind,
                            Buf    => Buf);
      else
         No_Data.Buffer_Alloc (Size => Size,
                               Buf  => Buf);
         Buf := Adjust_Back_No_Data_Id (Buf);
      end if;
   end Buffer_Alloc;

end AIP.Buffers;
