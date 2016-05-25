procedure Main is

   package P is
      procedure Dummy;
   end P;

   package body P is
      procedure Dummy is begin null; end;
   begin
      pragma Assert (for all X in Positive => X > 0);
   end P;

begin
   null;
end Main;
