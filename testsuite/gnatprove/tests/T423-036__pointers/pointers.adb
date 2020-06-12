package body Pointers is

   procedure Just_Read (Unused : Rec) with Global => null
   is
   begin
      null;
   end Just_Read;

   procedure Test is
      R : Rec;  -- @MEMORY_LEAK:FAIL
      S : Rec;  -- @MEMORY_LEAK:FAIL
      T : Rec;  -- @MEMORY_LEAK:FAIL
      U : Rec;  -- @MEMORY_LEAK:FAIL
      A : Int_Acc;
   begin
      R.X := new Integer'(0);
      R.Y := 0;

      A := new Integer'(0);
      S := (X => A, Y => 0);

      A := new Integer'(0);
      T :=
        (R with delta X => A);  -- @MEMORY_LEAK:FAIL
      T :=
        (T with delta Y => 0);  -- @MEMORY_LEAK:NONE
      R.X := new Integer'(0);
      A := new Integer'(0);
      U :=
        R'Update (X => A);  -- @MEMORY_LEAK:FAIL
      U :=
        U'Update (Y => 0);  -- @MEMORY_LEAK:NONE
      T :=
        ((T with delta Y => 0) with delta Y => 0);  -- @MEMORY_LEAK:NONE
      A := new Integer'(0);
      T :=
        ((T with delta Y => 0) with delta X => A);  -- @MEMORY_LEAK:FAIL
      A := new Integer'(0);
      T :=
        ((T with delta X => A) with delta Y => 0);  -- @MEMORY_LEAK:FAIL

      R.X := new Integer'(0);
      Just_Read (R);
      A := new Integer'(0);
      Just_Read ((X => A, Y => 42));
      Just_Read ((R with delta X => A));
      Just_Read ((R with delta Y => 0));
      Just_Read (((R with delta X => A) with delta X => A));
      Just_Read (R'Update (X => A));
      Just_Read (R'Update (Y => 0));
   end Test;

   procedure Test_List (L : in out List) is
   begin
      L := (L with delta Next => null);
   end Test_List;

end Pointers;
