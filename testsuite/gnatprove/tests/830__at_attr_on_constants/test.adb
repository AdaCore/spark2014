pragma Extensions_Allowed (All_Extensions);

--  Add a test with a reference to At containing a loop index in a local type
--  constraint.

procedure Test with SPARK_Mode
is
   function Id (X : Integer) return Integer is (X);
   X : Integer := 0;
begin
   for I in 1 .. 100 loop
      <<L1>>
      declare
         subtype T1 is Integer range 1 .. I'At (L1);
      begin
         X := X + I;
         pragma Loop_Invariant (X <= I * 100);
         pragma Assert (I in T1);
      end;
   end loop;
end;
