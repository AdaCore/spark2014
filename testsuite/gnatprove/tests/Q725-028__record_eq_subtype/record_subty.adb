procedure Record_Subty with SPARK_Mode is
   type R is record
      A, B : Integer;
   end record;

   function "=" (X, Y : R) return Boolean is (X.A = Y.A);

   subtype S is R;

   type RR is record
      C : S;
   end record;

   X : RR := (C => (A => 1, B => 1));
   Y : RR := (C => (A => 1, B => 2));
begin
   pragma Assert (X /= Y); --@ASSERT:FAIL
end Record_Subty;
