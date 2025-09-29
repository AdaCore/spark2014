procedure Main
  with Global => null
is

   --  Declare IGNORED and CHECKED ghost objects

   package A is
      pragma Assertion_Policy (Ghost => Ignore);
      Ignored : Boolean := True with Ghost;
   end;

   package B is
      pragma Assertion_Policy (Ghost => Check);
      Checked : Boolean := True with Ghost;
   end;

   use A, B;

   --  Each of those objects flows into itself, but without the explicit
   --  Depends contract we synthesize a safe approximation where every output
   --  depends on all allowed inputs.

   procedure Flip with Global => (In_Out => (Ignored, Checked)) is
   begin
      declare
         pragma Assertion_Policy (Ghost => Ignore);
      begin
         Ignored := not Ignored;
      end;
      declare
         pragma Assertion_Policy (Ghost => Check);
      begin
         Checked := not Checked;
      end;
   end;

   --  The synthesized dependency contract for Flip should match the explicit
   --  one on Test. These are the only legal assignments given the policies.

   procedure Test
     with Depends => (Ignored => (Ignored, Checked), Checked => Checked)
   is
   begin
      Flip;
   end;
begin
   Test;
end;
