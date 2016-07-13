package body Main is

   package body P is
      procedure Dummy is begin null; end;
   begin
      pragma Assert (for all X in Positive => X > 0);
      V.V := False;
   end P;

begin
   null;
end Main;
