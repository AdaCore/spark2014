procedure Main_Access with SPARK_Mode Is
   X : aliased Integer := 15 with Alignment => 4;
   Y : Integer with Import, Address => X'Address, Alignment => 4;
   C : aliased constant Integer := 15 with Alignment => 4;
   D : constant Integer with Import, Address => C'Address, Alignment => 4;

begin
   X := 15;
   declare
      O : access constant Integer := X'Access; --  Observe of an overlaid object
   begin
      Y := 12;
      pragma Assert (O.all = 15); -- This should not prove!
   end;

   declare
      B : access Integer := X'Access; --  Borrow of an overlaid object
   begin
      Y := 12;
   end;
   pragma Assert (X = 15); -- This should not prove!

   declare
      O : access constant Integer := C'Access; --  Everything is constant, it is OK
   begin
      null;
   end;
end Main_Access;
