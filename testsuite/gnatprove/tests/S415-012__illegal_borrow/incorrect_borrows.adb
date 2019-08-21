procedure Incorrect_Borrows with SPARK_Mode is
   type T1;
   type T1_Acc is access T1;
   type T1 is record
      B : Boolean;
      N : T1_Acc;
   end record
     with Predicate => (if T1.N /= null then T1.B /= T1.N.B);

   type T2;
   type T2_Acc is access T2;
   type T2_Acc_Array is array (Positive range <>) of T2_Acc;
   type T2_Acc_Array_Acc is access T2_Acc_Array;
   type T2 is record
      N : T2_Acc_Array_Acc (1 .. 2);
   end record;

   X1 : T1_Acc := new T1'(B => True, N => null);
   X2 : T1_Acc := new T1'(B => False, N => X1);
   X3 : T1_Acc := new T1'(B => True, N => X2);
   X  : T1_Acc := new T1'(B => False, N => X3);
begin
   declare
      Y : access T1 := X;
   begin
      Y := Y.N.N;
      Y.B := False;  --  Here we break the predicate
   end;
end Incorrect_Borrows;
