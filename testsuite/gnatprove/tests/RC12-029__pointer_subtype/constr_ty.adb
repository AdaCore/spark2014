procedure Constr_Ty (C : Natural) with SPARK_Mode is

   type A is array (Positive range <>) of Integer;

   type A_Acc is access A;
   subtype A_Acc_2 is A_Acc (1 .. 10);

   Z : A_Acc := new A'(1 .. C => 0);
   W : A_Acc_2 := Z; --@RANGE_CHECK:FAIL

   type R (X : Boolean) is null record;

   type R_Acc is access R;
   --  subtype R_Acc_2 is R_Acc (True);

   X : R_Acc := new R'(X => True);
   --  Y : R_Acc_2 := X;

begin
   for I in 1 .. C loop
      declare
         subtype A_Acc_3 is A_Acc (1 .. I);
         M : A_Acc := new A'(1 .. C => 1);
         N : A_Acc_3 := M; --@RANGE_CHECK:FAIL
      begin
         null;
      end;
   end loop;
   pragma Assert (for some E of W.all => E /= 0); --@ASSERT:FAIL
end Constr_Ty;
