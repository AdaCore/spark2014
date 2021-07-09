with Private_Type; use Private_Type;

procedure Main_Private_Rec is

   procedure Foo (X : Private_Rec) is
   begin
      null;
   end Foo;

   X : Private_Rec := Zero;

   procedure Bar (J : Private_Rec) with Global => null is
   begin
      for I in 1 .. 0 loop
         Foo (J);
      end loop;
   end Bar;

begin
   Bar (X);
end Main_Private_Rec;
