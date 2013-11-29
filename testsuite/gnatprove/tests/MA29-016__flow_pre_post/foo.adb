package body Foo with
   Refined_State => (State => (A, B, C))
is

   A : Integer;
   B : Integer;

   function Get_A return Integer is (A) with Refined_Global => A;

begin

   A := 1;
   B := 2;
   C := 3;

end Foo;
