procedure Main with SPARK_Mode is
   A : Boolean := False;
   B : Boolean := False;
   C : Boolean := True;
begin
   loop
      pragma Assert (not A or else B);
      A := True;
      pragma Loop_Invariant (A and then C);
      B := True;
      C := True;
      pragma Assert_And_Cut (B);
   end loop;
end Main;
