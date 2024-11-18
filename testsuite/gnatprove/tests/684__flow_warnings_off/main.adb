procedure Main with SPARK_Mode is
   X, Y : Integer;
   B : constant Boolean := False with Warnings => Off;
   procedure Foo with Global => (Output => X), Import, Always_Terminates;
   procedure Bar with Global => (Output => Y), Import, Always_Terminates;
   procedure Init with Pre => True;
   procedure Init is
   begin
      if B then
         Foo;
      end if;
      Bar;
   end Init;
begin
   Init;
end Main;
