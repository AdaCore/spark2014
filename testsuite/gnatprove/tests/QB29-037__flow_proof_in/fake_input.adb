procedure Fake_Input is

   S : Integer := 0;

   procedure Check with Global => (Input => S), Pre => S = 0 is
   begin
      pragma Assert (S = 0);
   end;

begin
   null;
end;
