procedure Main_Access with SPARK_Mode Is
   X : aliased Integer := 15 with Alignment => 4;
   Y : aliased Integer with Import, Address => X'Address, Alignment => 4;
   C : aliased constant Integer := 15 with Alignment => 4;
   D : aliased constant Integer with Import, Address => C'Address, Alignment => 4;

begin
   X := 15;
   declare
      O : access constant Integer := X'Access;
   begin
      Y := 12; --  X is observed, it cannot be written
      pragma Assert (O.all = 15); -- This should not prove!
   end;

   declare
      B : access Integer := X'Access;
   begin
      Y := 12; --  X is borrowed, it cannot be written
   end;
   pragma Assert (X = 15); -- This should not prove!

   Y := 15;
   declare
      O : access constant Integer := Y'Access; --  Observe of an overlaid object
   begin
      X := 12;
      pragma Assert (O.all = 15); -- This should not prove!
   end;

   declare
      B : access Integer := Y'Access; --  Borrow of an overlaid object
   begin
      X := 12;
   end;
   pragma Assert (Y = 15); -- This should not prove!

   declare
      O : access constant Integer := C'Access; --  Everything is constant, it is OK
   begin
      null;
   end;

   declare
      O : access constant Integer := D'Access; --  Everything is constant, it is OK
   begin
      null;
   end;
end Main_Access;
