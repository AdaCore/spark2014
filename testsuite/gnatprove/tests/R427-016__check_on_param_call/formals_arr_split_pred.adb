procedure Formals_Arr_Split_Pred with SPARK_Mode is
   type My_Array is array (Integer range <>) of Natural with
     Predicate => My_Array'First <= 1 and My_Array'Last >= 3;
   subtype Constr_Arr is My_Array with
     Predicate => Constr_Arr (3) /= 0;

   type Constr_Arr_2 is new My_Array with
     Predicate => Constr_Arr_2 (3) /= 0;

   procedure P (A : in out Constr_Arr) with
     Pre => True
   is
   begin
      A (1) := A (2) / A (3);
   end P;

   procedure P (A : in out Constr_Arr_2) with
     Pre => True
   is
   begin
      A (1) := A (2) / A (3);
   end P;

   procedure P2 (A : in out My_Array) with
     Pre => True
   is
   begin
      A (3) := 0;
   end P2;

   X : My_Array := (1 .. 10 => 1);
   Y : Constr_Arr := (1 .. 10 => 1);
   U : Constr_Arr_2 := (1 .. 10 => 1);
begin
   P (X);
   P2 (X);
   P2 (X);
   P (X); --@PREDICATE_CHECK:FAIL
   P2 (X);
   P (Constr_Arr (X)); --@PREDICATE_CHECK:FAIL
   P (Y);
   P2 (Y); --@PREDICATE_CHECK:FAIL
   P (Y);
   P2 (My_Array (Y)); --@PREDICATE_CHECK:FAIL
   P (U);
   P2 (My_Array (U)); --@PREDICATE_CHECK:FAIL
end Formals_Arr_Split_Pred;
