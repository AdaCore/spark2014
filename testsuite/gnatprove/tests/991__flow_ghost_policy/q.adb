package body Q is
   pragma Assertion_Policy (Ghost => Check);

   Hidden : Boolean with Ghost;

   procedure Set_Ignored_Ghost_Object is
   begin
      Hidden := True;
   end;
end;
