with Foo;

procedure Main
with
   SPARK_Mode,
   Global => (Output => Foo.State)
is
   Value : Natural := Natural'First;
begin
   pragma Warnings (Off, "attribute Valid is assumed to return True");
   --  pragma Warnings (Off);
   if Value'Valid then
      pragma Warnings (On, "attribute Valid is assumed to return True");
      --  pragma Warnings (On);
      Foo.Set_Data (Data => Value);
   else
      Value := 42;
      Foo.Set_Data (Data => Value);
   end if;

   pragma Assert (Foo.Get_Data = Value);
end Main;
