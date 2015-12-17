with Failsafe; use Failsafe;

procedure Test_Failsafe is

begin
   for J in 1 .. 49 loop
      Update (0.1);
   end loop;
   pragma Assert (not Is_Raised);
   Update (0.1);
   pragma Assert (Is_Raised);
   Update (0.1);
   pragma Assert (Is_Raised);
   Update (1.0);
   pragma Assert (not Is_Raised);
end Test_Failsafe;
