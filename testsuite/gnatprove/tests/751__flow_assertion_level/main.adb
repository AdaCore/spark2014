pragma Assertion_Level (L1);
pragma Assertion_Level (L2);

procedure Main
  with Global => null
is

   --  Create objects with declared ghost assertion levels

   Item1 : Boolean := True with Ghost => L1;
   Item2 : Boolean := True with Ghost => L2;

   --  Each of those objects flows into itself, but without the explicit
   --  Depends contract we synthesize a safe approximation where every output
   --  depends on all allowed inputs.

   procedure Flip
     with Global => (In_Out => (Item1, Item2))
   is
   begin
      Item1 := not Item1;
      Item2 := not Item2;
   end;

   --  The synthesized dependency contract for Flip should match the explicit
   --  one on Test. These are the only legal assignments given the policies.

   procedure Test
     with Depends => (Item1 => Item1,
                      Item2 => Item2)
   is
   begin
      Flip;
   end;
begin
   Test;
end;
