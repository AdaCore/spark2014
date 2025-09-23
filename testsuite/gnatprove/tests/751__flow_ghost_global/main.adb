--  This test uses ghost assertion levels to simulate what SPARK RM 6.9(26)
--  says about ghost policies (ignored and checked), i.e.:
--
--    If the Ghost assertion policy in effect at the point of the declaration
--    of a ghost variable or ghost state abstraction is Check, then the Ghost
--    assertion policy in effect at the point of any call to a procedural
--    subprogram for which that variable or state abstraction is a global
--    output shall be Check.
--
--  For flow, both ghost policies and ghost assertion levels restrict what
--  data dependencies are allowed, so they must really work the same.

pragma Assertion_Level (L_Checked);
pragma Assertion_Level (L_Ignored, Depends => L_Checked);

procedure Main is
   X_Checked : Boolean := True with Ghost => L_Checked;
   X_Ignored : Boolean := True with Ghost => L_Ignored;

   procedure Write_Checked with Ghost => L_Checked is
   begin
      X_Checked := True;
   end;

   procedure Write_Ignored with Ghost => L_Ignored is
   begin
      --  This assignment would be rejected:
      --
      --    X_Checked := True;
      --
      --  so an equivalent assignment via subprogram similar must be rejected
      --  as well:

      Write_Checked;
   end;

begin
   --  The following assignment would be rejected:
   --
   --    X_Checked := X_Ignored;
   --
   --  while an opposite assignment is legal:

   X_Ignored := X_Checked;  --  OK
end;
