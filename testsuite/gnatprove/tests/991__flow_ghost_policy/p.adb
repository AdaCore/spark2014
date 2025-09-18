with Q;

procedure P with SPARK_Mode is
   pragma Assertion_Policy (Ghost => Check);

   Visible_Checked : Boolean with Ghost;

   procedure Set_Visible_Checked_Ghost_Object with Ghost, Pre => True is
   begin
      Visible_Checked := True;
   end;

   pragma Assertion_Policy (Ghost => Ignore);

   procedure Test with Pre => True is
   begin
      Set_Visible_Checked_Ghost_Object;
      Q.Set_Hidden_Checked_Ghost_Object;
   end;
begin
   null;
end;
