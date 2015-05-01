package body P is

   --  unreferenced subprogram without aspect
   procedure Foo
   is
   begin
      null;
   end Foo;

   --  unreferenced subprogram with aspect
   procedure Bar
     with Pre => True
   is
   begin
      null;
   end Bar;

end P;
