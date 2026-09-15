pragma Extensions_Allowed (All_Extensions);

procedure Test (First, Later : Boolean; Output : out Boolean)
with
  SPARK_Mode,
  Depends => (Output => (First, Later))
is
   Value : Boolean := First;
begin
   Output := False;

   --  The first snapshot reads First. The assignment at the end of the loop
   --  makes every subsequent snapshot read Later.

   for Iteration in 1 .. 3 loop
      <<Capture>>
      Output := Output or Value'At (Capture);
      Value := Later;
   end loop;
end Test;
