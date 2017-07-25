procedure Test with SPARK_Mode is
   type R is record
      A, B : Integer;
   end record;

   type RR is record
      C : R;
   end record;

   X : RR := (C => (A => 1, B => 1));
   Y : RR := (C => (A => 1, B => 2));
   pragma Assert (X /= Y); --@ASSERT:PASS

   function "=" (X, Y : R) return Boolean is (X.A = Y.A);
begin
   pragma Assert (X /= Y); --@ASSERT:FAIL
end Test;
