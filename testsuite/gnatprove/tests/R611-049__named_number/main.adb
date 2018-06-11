procedure Main with SPARK_Mode
is
   procedure Proc
   is
      Foo : constant := 1 * 2 ** 31;
   begin
      null;
   end;
begin
   Proc;
end;
