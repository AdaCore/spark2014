procedure Main with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);

   subtype S1 is Integer with
     Predicate => Id (S1) > 0;
   subtype S2 is Integer with
     Predicate => S2 > 0;
   subtype S3 is S1 with
     Predicate => S3 mod 2 = 0;

   type T1 is new S1 with
     Predicate => T1 <= 100;
   type T2 is new S2 with
     Predicate => T2 <= 100;
   type T3 is new S3 with
     Predicate => T3 <= 100;

   type R is record
      X1 : T1 := T1 (Id (0)); --  predicate of S1 @PREDICATE_CHECK:FAIL
      X2 : T2 := T2 (Id (0)); --  predicate of S2 @PREDICATE_CHECK:FAIL
      X3 : T3 := T3 (Id (0)); --  predicate of S1 @PREDICATE_CHECK:FAIL
      X4 : T3 := T3 (Id (1)); --  predicate of S3 @PREDICATE_CHECK:FAIL
      X5 : T1 := T1 (Id (1000)); --  predicate of T1, not inherited @PREDICATE_CHECK:FAIL
      X6 : T2 := T2 (Id (1000)); --  predicate of T2, not inherited @PREDICATE_CHECK:FAIL
      X7 : T3 := T3 (Id (1000)); --  predicate of T3, not inherited @PREDICATE_CHECK:FAIL
   end record;

   type My_Arr is array (Positive range <>) of Natural with
     Predicate => My_Arr'First = 1;
   subtype Pos_Arr is My_Arr with
     Predicate => (for all E of Pos_Arr => E > 0);

   type Holder (L : Natural) is record
      Content : Pos_Arr (1 .. L);
   end record;

   procedure Test (X : in out Pos_Arr; I : Positive) with
     Pre => I in X'Range
   is
   begin
      X (I) := 0; --  predicate of Pos_Arr, not inherited @PREDICATE_CHECK:FAIL
   end Test;

   procedure Test (Y : in out Holder; I : Positive) with
     Pre => I <= Y.L
   is
   begin
      Y.Content (I) := 0; --  predicate of Pos_Arr, not inherited @PREDICATE_CHECK:FAIL
   end Test;

   X : R;
begin
   null;
end;
