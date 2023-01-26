procedure Main with SPARK_Mode is
   type Amount is record
      Raw : Natural;
   end record;

   procedure Test (A, B : Amount)
   with
     Post => Amount'(Raw => A.Raw - B.Raw) = Amount'(Raw => A.Raw - B.Raw),
     Global => null;

   ----------
   -- Test --
   ----------

   procedure Test (A, B : Amount) is null;

   Zero : constant Amount := (Raw => 0);
   Loan : constant Amount := (Raw => 1_000_000);
begin
   Test (Zero, Loan); --  computing 0 - 1_000_000 in Post won't fit in Natural
end;
