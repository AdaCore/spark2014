pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Jump                     :     Boolean;
   Before, After            :     Boolean;
   Snapshot_Output, Current : out Boolean)
with
  SPARK_Mode,
  Depends =>
    (Snapshot_Output => Before,
     Current         => (Jump, Before, After))
is
   Value : Boolean := Before;
begin
   <<Capture>>

   if Jump then
      goto Join;
   end if;

   Value := After;

   <<Join>>

   Snapshot_Output := Value'At (Capture);
   Current := Value;
end Test;
