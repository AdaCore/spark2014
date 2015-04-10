pragma Ada_2012;

package body Memory is

   type Slot is record
      Freed : Boolean;
      Next  : Address;
   end record;

   type Slots_T is array (Valid_Address) of Slot;

   Slots : Slots_T;

   Free_List : Address;

   function Next (A : Valid_Address) return Address is (Slots (A).Next);

   procedure Set_Next (A : Valid_Address; Next : Address) is
   begin
      Slots (A).Next := Next;
   end Set_Next;

   procedure Set_Freed (A : Valid_Address; Freed : Boolean) is
   begin
      Slots (A).Freed := Freed;
   end Set_Freed;

   function Model_F return Model_Free_List is
      pragma Postcondition
        --  The model and the concrete array Slots have the same freed elements
        ((for all E in Model_F'Result.Iterate =>
            Slots (Element (Model_F'Result, E)).Freed)
           and then
         (for all J in Valid_Address'Range =>
            (if Slots (J).Freed then Model_F'Result.Contains (J)))
           and then
         --  The model and the concrete free list match in order
         (for all E in Model_F'Result.Iterate =>
            (if Next (Model_F'Result, E) /= No_Element then
               Next (Element (Model_F'Result, E)) =
               Element (Model_F'Result, Next (Model_F'Result, E)))));

      L : Model_Free_List;
      A : Address := Free_List;
   begin
      while A /= Null_Address loop
         L.Append (Model_Address (A));
         A := Next (A);
      end loop;
      return L;
   end Model_F;

   function Alloc (Size : Positive) return Chunk is
      A   : Address := Free_List;
      S   : Natural := 0;
      Cur : Address;
      Pre : Address;
   begin
      Cur := A;
      Pre := Null_Address;
      while Cur /= Null_Address loop
         S := S + 1;

         --  If the expected size has been reached, return the chunk
         if S = Size then

            --  The chunk returned starts at the head of the free list. Just
            --  update the free list.
            if Free_List = A then
               Free_List := Next (Cur);
            --  The chunk starts at the middle of the free list. Relink the
            --  slot preceding it.
            else
               Set_Next (Pre, Next (Cur));
            end if;

            --  Mark the slots in the chunk as allocated and return it.
            Set_Next (Cur, Null_Address);

            Cur := A;
            while Cur /= Null_Address loop
               Set_Freed (Cur, False);
               Cur := Next (Cur);
            end loop;

            return Chunk'(Addr => A, Size => Size);
         end if;

         --  If the next slot is not contiguous, restart from next slot
         if Next (Cur) /= Cur + 1 then
            Pre := Cur;
            A   := Next (Cur);
            S   := 0;
         end if;

         Cur := Next (Cur);
      end loop;

      --  Allocation failed, return the null chunk
      return Null_Chunk;
   end Alloc;

   procedure Free (C : Chunk) is
      A   : constant Address := C.Addr;
      Cur : Address;
   begin
      --  Mark the slots in the chunk as freed
      Cur := A;
      while Next (Cur) /= Null_Address loop
         Set_Freed (Cur, True);
         Cur := Next (Cur);
      end loop;
      Set_Freed (Cur, True);

      --  Put the chunk at the head of the free list
      Set_Next (Cur, Free_List);
      Free_List := A;
   end Free;

--  Initialize the free list
begin
   for J in Slots'First .. Slots'Last - 1 loop
      Slots (J) := Slot'(Freed => True, Next => J + 1);
   end loop;
   Slots (Slots'Last) := Slot'(Freed => True, Next => Null_Address);
   Free_List := Slots'First;
end Memory;
