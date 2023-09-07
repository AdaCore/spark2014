procedure P (X : Integer) with SPARK_Mode is
begin
   pragma Assert (X > 0, "X should be positive at this point");
   pragma Assert_And_Cut (X > 5, "X should be > 5 at this point");
   loop
      pragma Loop_Invariant (X > 10, "X should be > 10 at this point");
      pragma Loop_Invariant (X > 15, "X should be > 15 at this point");
   end loop;
end;
