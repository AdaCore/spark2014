with Q;
procedure P with SPARK_Mode is
   pragma Assertion_Policy (Ghost => Check);
   X : Integer := 15 with Ghost;
   procedure P with Ghost, Post => X = 0;
   procedure P is
   begin
      X := 0;
      Q.Set_Ignored_Ghost_Object;
   end P;
   pragma Assertion_Policy (Ghost => Ignore);
   procedure P2 with Ghost, Post => X = 0;
   procedure P2 is
   begin
      P;
   end P2;
begin
   P2;
   declare
      pragma Assertion_Policy (Ghost => Check);
      pragma Assertion_Policy (Assert => Check);
   begin
      pragma Assert (X = 0);
   end;
end;
