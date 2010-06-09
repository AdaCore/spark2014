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
         Result := No_Data.Buffer_Tlen (Adjust_No_Data_Id (Buf));
      end if;
      return Result;
   end Buffer_Len;

   -----------------
   -- Buffer_Tlen --
   -----------------

   function Buffer_Tlen (Buf : Buffer_Id) return AIP.U16_T
   --# global in Data.State, No_Data.State;
   is
      Result : AIP.U16_T;
   begin
      if Is_Data_Buffer (Buf) then
         Result := Data.Buffer_Tlen (Buf);
      else
         Result := No_Data.Buffer_Tlen (Adjust_No_Data_Id (Buf));
      end if;
      return Result;
   end Buffer_Tlen;

   -----------------
   -- Buffer_Next --
   -----------------

   function Buffer_Next (Buf : Buffer_Id) return Buffer_Id
   --# global in Data.State;
   is
      Result : Buffer_Id;
   begin
      if Is_Data_Buffer (Buf) then
         Result := Data.Buffer_Next (Buf);
      else
         Result := NOBUF;
      end if;
      return Result;
   end Buffer_Next;

   --------------------
   -- Buffer_Payload --
   --------------------

   function Buffer_Payload (Buf : Buffer_Id) return AIP.IPTR_T
   --# global in Data.State, No_Data.State;
   is
      Result : AIP.IPTR_T;
   begin
      if Is_Data_Buffer (Buf) then
         Result := Data.Buffer_Payload (Buf);
      else
         Result := No_Data.Buffer_Payload (Adjust_No_Data_Id (Buf));
      end if;
      return Result;
   end Buffer_Payload;

   ----------------
   -- Buffer_Ref --
   ----------------

   procedure Buffer_Ref (Buf : Buffer_Id)
   --# global in out Data.State, No_Data.State;
   is
   begin
      if Is_Data_Buffer (Buf) then
         Data.Buffer_Ref (Buf);
      else
         No_Data.Buffer_Ref (Adjust_No_Data_Id (Buf));
      end if;
   end Buffer_Ref;

   -----------------
   -- Buffer_Free --
   -----------------

   procedure Buffer_Free (Buf : Buffer_Id; N_Deallocs : out AIP.U8_T)
   --# global in out Data.State, No_Data.State;
   is
      Dealloc : Boolean;
   begin
      if Is_Data_Buffer (Buf) then
         Data.Buffer_Free (Buf, N_Deallocs);
      else
         No_Data.Buffer_Free (Adjust_No_Data_Id (Buf), Dealloc);
         if Dealloc then
            N_Deallocs := 1;
         else
            N_Deallocs := 0;
         end if;
      end if;
   end Buffer_Free;

   -----------------------
   -- Buffer_Blind_Free --
   -----------------------

   procedure Buffer_Blind_Free (Buf : Buffer_Id)
   --# global in out Data.State, No_Data.State;
   is
      N_Deallocs : AIP.U8_T;
   begin
      --# accept F, 10, N_Deallocs, "Assignment is ineffective";
      Buffer_Free (Buf, N_Deallocs);
      --# end accept;
      --# accept F, 33, N_Deallocs,
      --#               "The variable is neither referenced nor exported";
   end Buffer_Blind_Free;

   --------------------
   -- Buffer_Release --
   --------------------

   procedure Buffer_Release (Buf : Buffer_Id)
   --# global in out Data.State, No_Data.State;
   is
      N_Deallocs : AIP.U8_T := 0;
   begin
      --  Keep calling Buffer_Free until it deallocates
      while N_Deallocs = 0 loop
         Buffer_Free (Buf, N_Deallocs);
      end loop;
   end Buffer_Release;

end AIP.Buffers;
