procedure Foo (X : Integer) with SPARK_Mode is
   package Bar is
      Y : constant Integer;
   private
      Y : constant Integer := X;
   end Bar;
   subtype Baz is Integer range Bar.Y .. Bar.Y; --  Assert_Failure
begin
   null;
end Foo;
