package body Q is
   pragma Assertion_Policy (Ghost => Check);

   Hidden_Checked : Boolean with Ghost;

   procedure Set_Hidden_Checked_Ghost_Object is
   begin
      Hidden_Checked := True;
   end;
end;
