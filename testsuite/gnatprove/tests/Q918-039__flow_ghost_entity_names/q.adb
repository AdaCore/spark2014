package body Q is
   F : Integer with Ghost;
   G : Integer ;

   procedure Foo (X : Integer)
   is
   begin
      G := X; -- non-ghost global output
   end;

   procedure Bar (X : Integer)
   is
   begin
      F := X; -- ghost global output
   end;
end;
