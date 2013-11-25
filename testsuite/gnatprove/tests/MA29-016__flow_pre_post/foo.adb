package body Foo with
   Refined_State => (State => (A, B, C))
is

   A : Integer;
   B : Integer;

begin

   A := 1;
   B := 2;
   C := 3;

end Foo;
