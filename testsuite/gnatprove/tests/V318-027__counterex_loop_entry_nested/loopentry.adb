package body LoopEntry is

   ----------------------------------------
   -- Increment_Array_Nested_Loop_Simple --
   ----------------------------------------

   procedure Increment_Array_Nested_Loop_Simple (A : in out Int_Array) is
   begin
      Outter: for J in A'Range loop
         A(J) := A(J) + 1;
         Inner: for K in Int(1) .. Int(1) loop   --  Only loop once
            A(J) := A(J) + K;
            pragma Assert (A(J) = A'Loop_Entry(J) + 1);            --  @ASSERT:PASS
            --  Correct since A'Loop_Entry refers to the value of A upon entry
            --  of the nearest loop. Since then the value of element A(J)
            --  has only been incremented once during the first iteration.
            pragma Assert (A(J) = A'Loop_Entry(J) + 2);            --  @ASSERT:FAIL
            --  Fails on the first iteration as A(J) has only been incremented
            --  once in the nearest loop.
         end loop Inner;
      end loop Outter;
   end Increment_Array_Nested_Loop_Simple;

   ---------------------------------------
   -- Increment_Array_Nested_Loop_Inner --
   ---------------------------------------

   procedure Increment_Array_Nested_Loop_Inner (A : in out Int_Array) is
   begin
      Outter: for J in A'Range loop
         A(J) := A(J) + 1;
         Inner: for K in Int(1) .. Int(1) loop   --  Only loop once
            A(J) := A(J) + K;
            pragma Assert (A(J) = A'Loop_Entry(Inner)(J) + 1);     --  @ASSERT:PASS
            pragma Assert (A(J) = A'Loop_Entry(Inner)(J) + 2);     --  @ASSERT:FAIL
            --  Equivalent to using A'Loop_Entry, should behave like the
            --  previous function.
         end loop Inner;
      end loop Outter;
   end Increment_Array_Nested_Loop_Inner;

   ----------------------------------------
   -- Increment_Array_Nested_Loop_Outter --
   ----------------------------------------

   procedure Increment_Array_Nested_Loop_Outter (A : in out Int_Array) is
   begin
      Outter: for J in A'Range loop
         A(J) := A(J) + 1;
         Inner: for K in Int(1) .. Int(1) loop   --  Only loop once
            A(J) := A(J) + K;
            pragma Assert (A(J) = A'Loop_Entry(Outter)(J) + 2);    --  @ASSERT:PASS
            pragma Assert (A(J) = A'Loop_Entry(Outter)(J) + 1);    --  @ASSERT:FAIL
            -- A(J) has been incremented twice since entry in Outter loop.
         end loop Inner;
      end loop Outter;
   end Increment_Array_Nested_Loop_Outter;

   -----------------
   -- Very_Nested --
   -----------------

   procedure Very_Nested (A : in out Int_Array) is
   begin
      One: for J in A'Range loop
         A(J) := A(J) + 1;
         Two: for K in Int(1) .. Int(1) loop   --  Only loop once
            A(J) := A(J) + K;
            Three: for L in Int(1) .. Int(1) loop   -- Only loop once
               A(J) := A(J) + K;
               pragma Assert (A(J) = A'Loop_Entry(One)(J) + 3);    --  @ASSERT:PASS
               pragma Assert (A(J) = A'Loop_Entry(Three)(J) + 1);  --  @ASSERT:PASS
               pragma Assert (A(J) = A'Loop_Entry(Two)(J) + 1);    --  @ASSERT:FAIL
               -- A(J) has been incremented twice since entry in Three loop.
            end loop Three;
         end loop Two;
      end loop One;
   end Very_Nested;

   -----------------------------
   -- Loop_Entry_In_Loop_Spec --
   -----------------------------

   procedure Loop_Entry_In_Loop_Spec (I : in out Int) is
   begin
      for J in Int(1) .. Int(1) loop   --  Only loop once
         I := I + 1;
         pragma Assert (for all K in 1 .. I'Loop_Entry => K /= K); --  @ASSERT:FAIL
      end loop;
   end Loop_Entry_In_Loop_Spec;

end LoopEntry;
