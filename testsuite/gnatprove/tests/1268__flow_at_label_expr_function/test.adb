pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Value, Later, Global_Input, Proof, Unused : Integer; Output : out Boolean)
with
  SPARK_Mode,
  Pre     => Proof > 1,
  Depends =>
    (Output => (Value, Global_Input), null => (Later, Proof, Unused))
is
   function Pick (Item, Checked : Integer) return Boolean with
     Global  => (Input => Global_Input, Proof_In => Proof),
     Pre     => Proof > 0,
     Depends => (Pick'Result => (Item, Global_Input), null => Checked);

   function Pick (Item, Checked : Integer) return Boolean is
   begin
      pragma Assert (Proof /= 0);
      return Item = Global_Input;
   end Pick;

   X : Integer := Value;
begin
   <<Capture>>
   X := Later;
   Output := Boolean'(Pick (X, Unused) and then True)'At (Capture);
end Test;
