package body Q is
   protected body PO is
      procedure Foo is null;
   end PO;
begin
   PO.Foo;
end Q;
