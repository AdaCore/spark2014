procedure Main_Rec is

   type Rec is record
      A, B : Integer;
   end record;

   procedure Foo (X : Rec) is
   begin
      null;
   end Foo;

   X : Rec := (0, 0);

   procedure Bar (J : Rec) with Global => null is
   begin
      for I in 1 .. 0 loop
         Foo (J);
      end loop;
   end Bar;

begin
   Bar (X);
end Main_Rec;
