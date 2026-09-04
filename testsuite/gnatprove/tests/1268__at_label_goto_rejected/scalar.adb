pragma Extensions_Allowed (All_Extensions);

procedure Scalar
  (Choose_First, First, Second : Boolean; Output : out Boolean)
with SPARK_Mode
is
   Value : Boolean;
begin
   --  A label referenced by multiple gotos cannot also define a snapshot

   if Choose_First then
      Value := First;
      goto Capture;
   else
      Value := Second;
      goto Capture;
   end if;

   <<Capture>>
   Output := Value'At (Capture);
end Scalar;
