pragma Extensions_Allowed (All_Extensions);

procedure Loop_Snapshot
  (First, Later : Boolean; Output : out Boolean)
with SPARK_Mode
is
   Value : Boolean := First;
begin
   Output := False;

   --  A goto cannot enter a snapshot label on each loop iteration

   for Iteration in 1 .. 3 loop
      goto Capture;

      <<Capture>>
      Output := Output or Value'At (Capture);
      Value := Later;
   end loop;
end Loop_Snapshot;
