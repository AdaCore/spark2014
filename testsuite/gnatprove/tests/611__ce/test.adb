procedure Test with SPARK_Mode is
   type Int_Arr is array (Positive range <>) of Integer;

   procedure Test_Eq (I, J : Positive) with Global => null is
      X : Int_Arr (J .. J) := (others => 1);
      Y : Int_Arr (J .. J) := (others => 0);
   begin
      X (J) := I;
      pragma Assert (X = Y); --@ASSERT:FAIL @COUNTEREXAMPLE
   end Test_Eq;

   procedure Test_Inv_1 (I : Positive) with Global => null is
      X : Int_Arr (1 .. 10) := (others => 1);
   begin
      for K in 1 .. 10 loop
         pragma Loop_Invariant (for all H in 1 .. K => X (H) = I); --@LOOP_INVARIANT_INIT:FAIL @COUNTEREXAMPLE
         X (K) := I;
      end loop;
   end Test_Inv_1;

   procedure Test_Inv_2 (I : Positive) with Global => null is
      X : Int_Arr (1 .. 10) := (others => 1);
   begin
      for K in 1 .. 10 loop
         pragma Loop_Invariant (for all H in 1 .. K => X (H) = 1); --@LOOP_INVARIANT_PRESERV:FAIL @COUNTEREXAMPLE
         X (K) := I;
      end loop;
   end Test_Inv_2;

   procedure Test_Inv_3 (I, J : Positive) with Global => null is
      X : Int_Arr (1 .. 10) := (others => 1);
   begin
      for K in 1 .. 10 loop
         pragma Loop_Invariant (for all H in 1 .. K => X (H) = I); --@LOOP_INVARIANT_INIT:FAIL @LOOP_INVARIANT_PRESERV:FAIL @COUNTEREXAMPLE
         X (K) := J;
      end loop;
   end Test_Inv_3;

begin
   null;
end Test;
