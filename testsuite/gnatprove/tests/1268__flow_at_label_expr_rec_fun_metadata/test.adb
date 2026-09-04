pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Value, Later, Global_Input, Proof, Unused : Integer;
   Output                                    : out Boolean)
with
  SPARK_Mode,
  Pre     => Proof > 1,
  Depends =>
    (Output => (Value, Global_Input), null => (Later, Proof, Unused))
is
   type Pair is record
      Selected : Boolean;
      Other    : Integer;
   end record;

   function Pick (Item, Checked : Integer) return Pair
   with
     Global  => (Input => Global_Input, Proof_In => Proof),
     Pre     => Proof > 0,
     Depends => (Pick'Result => (Item, Global_Input), null => Checked);

   function Pick (Item, Checked : Integer) return Pair is
   begin
      pragma Assert (Proof /= 0);
      return (Selected => Item = Global_Input, Other => Item);
   end Pick;

   X : Integer := Value;

begin
   <<Capture>>
   X := Later;
   Output := Pick (X, Unused)'At (Capture).Selected;
end Test;
