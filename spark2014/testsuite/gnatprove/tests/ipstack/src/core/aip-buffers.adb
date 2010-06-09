------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Buffers.Common;
with AIP.Buffers.Data;
with AIP.Buffers.No_Data;

package body AIP.Buffers
--# own State is AIP.Buffers.Common.Buf_List,
--#              AIP.Buffers.Data.State, AIP.Buffers.Data.Free_List,
--#              AIP.Buffers.No_Data.State, AIP.Buffers.No_Data.Free_List;
is
   --------------------
   -- Is_Data_Buffer --
   --------------------

   function Is_Data_Buffer (Buf : Buffer_Id) return Boolean is
   begin
      return Buf <= Chunk_Num;
   end Is_Data_Buffer;

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Offset :     Offset_Length;
      Size   :     Data_Length;
      Kind   :     Buffer_Kind;
      Buf    : out Buffer_Id)
   --# global in out Common.Buf_List,
   --#               Data.State, Data.Free_List,
   --#               No_Data.State, No_Data.Free_List;
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
         Buf := No_Data.Adjust_Back_Id (No_Data_Buf);
      end if;
   end Buffer_Alloc;

   ----------------
   -- Buffer_Len --
   ----------------

   function Buffer_Len (Buf : Buffer_Id) return AIP.U16_T
   --# global in Common.Buf_List;
   is
   begin
      return Common.Buf_List (Buf).Len;
   end Buffer_Len;

   -----------------
   -- Buffer_Tlen --
   -----------------

   function Buffer_Tlen (Buf : Buffer_Id) return AIP.U16_T
   --# global in Common.Buf_List;
   is
   begin
      return Common.Buf_List (Buf).Tot_Len;
   end Buffer_Tlen;

   -----------------
   -- Buffer_Next --
   -----------------

   function Buffer_Next (Buf : Buffer_Id) return Buffer_Id
   --# global in Common.Buf_List;
   is
   begin
      return Common.Buf_List (Buf).Next;
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
         Result := No_Data.Buffer_Payload (No_Data.Adjust_Id (Buf));
      end if;
      return Result;
   end Buffer_Payload;

   ----------------
   -- Buffer_Ref --
   ----------------

   procedure Buffer_Ref (Buf : Buffer_Id)
   --# global in out Common.Buf_List;
   is
   begin
      Common.Buf_List (Buf).Ref := Common.Buf_List (Buf).Ref + 1;
   end Buffer_Ref;

   -----------------
   -- Buffer_Free --
   -----------------

   procedure Buffer_Free (Buf : Buffer_Id; N_Deallocs : out AIP.U8_T)
   --# global in out Common.Buf_List, Data.State,
   --#               Data.Free_List, No_Data.Free_List;
   is
      Cur_Buf, Next_Buf : Buffer_Id;
      Free_List         : Buffer_Index;
   begin
      Next_Buf   := Buf;
      N_Deallocs := 0;

      while Next_Buf /= NOBUF loop
         --  Update iterators
         Cur_Buf  := Next_Buf;
         Next_Buf := Common.Buf_List (Cur_Buf).Next;

         --  Store head of appropriate free-list in Free_List
         if Is_Data_Buffer (Cur_Buf) then
            Free_List := Data.Free_List;
         else
            Free_List := No_Data.Adjust_Back_Id (No_Data.Free_List);
         end if;

         --  Decrease reference count
         Common.Buf_List (Cur_Buf).Ref := Common.Buf_List (Cur_Buf).Ref - 1;

         --  If reference count reaches zero, deallocate buffer
         if Common.Buf_List (Cur_Buf).Ref = 0 then
            N_Deallocs                     := N_Deallocs + 1;

            --  Link to the head of the free-list
            Common.Buf_List (Cur_Buf).Next := Free_List;

            --  Perform link actions specific to data buffers
            if Is_Data_Buffer (Cur_Buf) then
               Data.Buffer_Link (Cur_Buf, Free_List);
            end if;

            --  Push to the head of the appropriate free-list
            if Is_Data_Buffer (Cur_Buf) then
               Data.Free_List              := Cur_Buf;
            else
               No_Data.Free_List           := No_Data.Adjust_Id (Cur_Buf);
            end if;
         else
            --  Stop the iteration
            Next_Buf                       := NOBUF;
         end if;
      end loop;
   end Buffer_Free;

   -----------------------
   -- Buffer_Blind_Free --
   -----------------------

   procedure Buffer_Blind_Free (Buf : Buffer_Id)
   --# global in out Common.Buf_List, Data.State,
   --#               Data.Free_List, No_Data.Free_List;
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
   --# global in out Common.Buf_List, Data.State,
   --#               Data.Free_List, No_Data.Free_List;
   is
      N_Deallocs : AIP.U8_T := 0;
   begin
      --  Keep calling Buffer_Free until it deallocates
      while N_Deallocs = 0 loop
         Buffer_Free (Buf, N_Deallocs);
      end loop;
   end Buffer_Release;

end AIP.Buffers;
