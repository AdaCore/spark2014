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
      --  Reference to the actual data
      Payload_Ref : System.Address;
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
         Result := U16_T (Buf - Config.Data_Buffer_Num);
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
         Result := AIP.U16_T (Buf) + Config.Data_Buffer_Num;
      end if;
      return Result;
   end Adjust_Back_Id;

   -----------------
   -- Buffer_Init --
   -----------------

   procedure Buffer_Init
   --# global out Buf_List, Free_List;
   is
   begin
      --  Initialize all the memory for buffers to zero

      Buf_List := Buffer_Array'
                    (others => Buffer'(Payload_Ref => System.Null_Address));

      --  Make the head of the free-list point to the first buffer

      Free_List := Buf_List'First;
   end Buffer_Init;

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

      Common.Buf_List (Adjusted_Buf).Next    := Buffers.NOBUF;
      Common.Buf_List (Adjusted_Buf).Len     := Size;
      Common.Buf_List (Adjusted_Buf).Tot_Len := Size;
      --  Set reference count
      Common.Buf_List (Adjusted_Buf).Ref     := 1;

      --  Set specific fields

      --  Caller must set this field properly, afterwards
      Buf_List (Buf).Payload_Ref             := System.Null_Address;
   end Buffer_Alloc;

   --------------------
   -- Buffer_Payload --
   --------------------

   function Buffer_Payload (Buf : Buffer_Id) return System.Address
   --# global in Buf_List;
   is
   begin
      return Buf_List (Buf).Payload_Ref;
   end Buffer_Payload;

   -------------------
   -- Buffer_Header --
   -------------------

   procedure Buffer_Header
     (Buf  : Buffer_Id;
      Bump : AIP.S16_T;
      Err  : in out AIP.Err_T)
   --# global in out Buf_List;
   is
   begin
      --  Check that we are not going to move off the beginning of the buffer
      Support.Verify_Or_Err (Bump <= 0, Err, AIP.ERR_MEM);

      if Err = AIP.NOERR then
         Buf_List (Buf).Payload_Ref :=
           Conversions.Ofs (Buf_List (Buf).Payload_Ref, Integer (-Bump));
      end if;
   end Buffer_Header;

end AIP.Buffers.No_Data;
