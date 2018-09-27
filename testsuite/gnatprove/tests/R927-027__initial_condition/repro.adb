package body Repro
with
  Refined_State => (State => (A,B))
is

   A, B : Integer := 0;

   -----------------------------------------------------------------------------

   function Invariant return Boolean
   is (A >= 0 and then B <= 0 and then A + B = 0);

   -----------------------------------------------------------------------------

   procedure Foo
   is
   begin
      if A < Integer'Last and B > Integer'First then
         A := A + 1;
         B := B - 1;
      else
         A := 0;
         B := 0;
      end if;
   end Foo;

end Repro;
