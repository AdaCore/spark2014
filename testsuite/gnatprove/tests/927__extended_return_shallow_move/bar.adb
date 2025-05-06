procedure Bar with SPARK_Mode is
   type L is limited record
      Field : Integer;
   end record;
   function Foo return L with Post => (Foo'Result.Field = 1);
   function Foo return L is
   begin
      return X : aliased L := (Field => 1) do
         declare
            type A is access all L;
            Y : A := X'Access;
         begin
            Y.Field := 0;
         end;
      end return;
   end Foo;
begin
   null;
end Bar;
