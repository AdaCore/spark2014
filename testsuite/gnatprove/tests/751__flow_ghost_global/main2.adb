--  This test is identical to Main, but with dummy contracts that prevent
--  inlining-for-proof.

pragma Assertion_Level (L_Checked);
pragma Assertion_Level (L_Ignored, Depends => L_Checked);

procedure Main2 is
   X_Checked : Boolean := True with Ghost => L_Checked;
   X_Ignored : Boolean := True with Ghost => L_Ignored;

   procedure Write_Checked with Ghost => L_Checked, Pre => True is
   begin
      X_Checked := True;
   end;

   procedure Write_Ignored with Ghost => L_Ignored, Pre => True is
   begin
      Write_Checked;
   end;

begin
   X_Ignored := X_Checked;  --  OK
end;
