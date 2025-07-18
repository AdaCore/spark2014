package body Simple is

   procedure Foo (X : in out Outer) is
   begin
      Bar (Inner (X.Z.all));            --  Error.
   end Foo;

   procedure Bar (Y : in out Inner) is  --  Removing "out" will finish the analysis.
   begin
      null;
   end Bar;

end Simple;
