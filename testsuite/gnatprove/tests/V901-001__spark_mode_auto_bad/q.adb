with P; use P;

procedure Q with SPARK_Mode => Auto is
   pragma SPARK_Mode (Auto);
   X : P.Good := 42;

   procedure Local with SPARK_Mode => Auto is
   begin
      null;
   end;
begin
   pragma Assert (X = 42);
end Q;
