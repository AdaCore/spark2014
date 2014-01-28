procedure Foo (X : out Integer)
is
begin
   X := 10;
   pragma Inspection_Point;
   X := X + 1;
   X := X / 2;
end Foo;
