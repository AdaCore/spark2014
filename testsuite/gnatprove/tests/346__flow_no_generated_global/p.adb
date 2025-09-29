package body P
  with Refined_State => (Full_State => (Private_State, Body_State))
is
   Body_State : Boolean := True;

   function Read_Private_And_Body_State return Boolean
   with Refined_Global => (Input => (Private_State, Body_State))
   is
   begin
      return Private_State and Body_State;
   end;

end;
