package body LoopEntry is

   function Same (I : in Int) return Int is
   begin
      return I;
   end Same;

   function Same (A : in Int_Array) return Int_Array is
   begin
      return A;
   end Same;

   ---------------
   -- Increment --
   ---------------

   procedure Increment_Assert (I : in out Int) is
   begin
      for J in 1 .. 3 loop
         I := I + 1;
         pragma Assert (I = I'Loop_Entry);                         --  @ASSERT:FAIL
      end loop;
   end Increment_Assert;

   procedure Increment_Invariant (I : in out Int) is
   begin
      for J in 1 .. 3 loop
         I := I + 1;
         pragma Loop_Invariant (I = I'Loop_Entry);                 --  @LOOP_INVARIANT_INIT:FAIL @LOOP_INVARIANT_PRESERV:FAIL
      end loop;
   end Increment_Invariant;

   ---------------------
   -- Increment_Array --
   ---------------------

   procedure Increment_Array_Assert (A : in out Int_Array) is
   begin
      for J in A'Range loop
         A(J) := A(J) + 1;

         pragma Assert (A(J) = A'Loop_Entry(J) - 1);               --  @ASSERT:FAIL
      end loop;
   end Increment_Array_Assert;

   procedure Increment_Array_Invariant (A : in out Int_Array) is
   begin
      for J in A'Range loop
         A(J) := A(J) + 1;

         pragma Loop_Invariant (for all K in A'First .. J =>
                                 A(K) = A'Loop_Entry(K) + 2);      --  @LOOP_INVARIANT_INIT:FAIL @LOOP_INVARIANT_PRESERV:FAIL
      end loop;
   end Increment_Array_Invariant;

   ------------------------
   -- Loop_Entry_On_Call --
   ------------------------

   procedure Loop_Entry_On_Call_Assert (A : in out Int_Array)
   is
      pragma Unevaluated_Use_Of_Old (Allow);
   begin
      for J in A'Range loop
         A(J) := A(J) + 1;

         pragma Assert (A(J) = Same (A)'Loop_Entry(J) - 1);        --  @ASSERT:FAIL
      end loop;
   end Loop_Entry_On_Call_Assert;

   procedure Loop_Entry_On_Call_Invariant (A : in out Int_Array)
   is
      pragma Unevaluated_Use_Of_Old (Allow);
   begin
      for J in A'Range loop
         A(J) := A(J) + 1;

         pragma Loop_Invariant (for all K in A'First .. J =>
                                 A(K) = Same (A)'Loop_Entry(K));   --  @LOOP_INVARIANT_INIT:FAIL @LOOP_INVARIANT_PRESERV:FAIL
      end loop;
   end Loop_Entry_On_Call_Invariant;

   ---------------------------------
   -- Loop_Entry_On_Arr_In_Record --
   ---------------------------------

   procedure Loop_Entry_On_Arr_In_Record_Assert (R : in out Array_Record) is
   begin
      for J in R.A'Range loop
         R.A(J) := R.A(J) + 1;

         pragma Assert (R.A(J) = R.A'Loop_Entry(J) - 1);           --  @ASSERT:FAIL
      end loop;
   end Loop_Entry_On_Arr_In_Record_Assert;

   procedure Loop_Entry_On_Arr_In_Record_Invariant (R : in out Array_Record) is
   begin
      for J in R.A'Range loop
         R.A(J) := R.A(J) + 1;

         pragma Loop_Invariant (for all K in R.A'First .. J =>
                                 R.A(K) = R.A'Loop_Entry(K));      --  @LOOP_INVARIANT_INIT:FAIL @LOOP_INVARIANT_PRESERV:FAIL
      end loop;
   end Loop_Entry_On_Arr_In_Record_Invariant;

   ------------------------------
   -- Loop_Entry_In_Call_Param --
   ------------------------------

   procedure Loop_Entry_In_Call_Param (I : in Int) is
   begin
      for J in 1 .. 3 loop
         pragma Assert (Same(I'Loop_Entry) /= I);                  --  @ASSERT:FAIL
      end loop;
   end Loop_Entry_In_Call_Param;

end LoopEntry;
