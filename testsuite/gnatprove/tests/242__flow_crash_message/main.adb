procedure Main with SPARK_Mode is
   type List;
   type List_Acc is access List;
   type List is record
      D : Integer;
      N : List_Acc;
   end record;

   procedure Contains (L : not null access List) is
   begin
      null;
   end Contains;

   procedure Foo (I : not null access Integer) is
   begin
      null;
   end Foo;
begin
   null;
end Main;
