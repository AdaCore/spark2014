procedure Test_Init_By_Proof_Mem with SPARK_Mode is
   function Branch (X : Integer) return Boolean with
     Import;
   type My_Int is new Integer with
     Relaxed_Initialization;
   subtype My_Nat is My_Int range 0 .. 10;

   type Rec_2 (D : My_Int) is record
      X : Integer;
      Y : My_Int;
      Z : Boolean;
   end record with
     Relaxed_Initialization;
   subtype Rec_3 is Rec_2 (15);

   type My_Arr is array (Positive range <>) of Natural;
   type My_Arr_2 is new My_Arr with
     Relaxed_Initialization;
   subtype My_Arr_3 is My_Arr_2 (15 .. 18);

   X1 : Rec_2 (15);
   X2 : Rec_2 (15) := (15, 1, 1, True);
   Y1 : My_Int;
   Y2 : My_Int := 1;
   Z1 : My_Arr_2 (15 .. 18);
   Z2 : My_Arr_2 (15 .. 18) := (others => 1);
begin
   if Branch (1) then
      pragma Assert (X1 in Rec_3); --@INIT_BY_PROOF:NONE
      pragma Assert (Z1 in My_Arr_3); --@INIT_BY_PROOF:NONE
      pragma Assert (Y1 in My_Nat); --@INIT_BY_PROOF:FAIL
   elsif Branch (2) then
      pragma Assert (X2 in Rec_3);
      pragma Assert (Z2 in My_Arr_3);
      pragma Assert (Y2 in My_Nat);
   elsif Branch (3) then
      pragma Assert (X1 in Rec_3 | X2); --@INIT_BY_PROOF:FAIL
      pragma Assert (Z1 in My_Arr_3 | Z2); --@INIT_BY_PROOF:FAIL
   else
      pragma Assert (X2 in Rec_3 | X1);
      pragma Assert (Z2 in My_Arr_3 | Z1);
   end if;
end Test_Init_By_Proof_Mem;
