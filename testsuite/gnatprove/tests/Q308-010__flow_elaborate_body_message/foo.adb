procedure Foo with Global => null
is
begin

   declare
      package P with Initializes => V is
         V : Integer := 3;
      end P;

      package body P is
      begin
         V := V * 3;
      end P;
   begin
      null;
   end;

end Foo;
