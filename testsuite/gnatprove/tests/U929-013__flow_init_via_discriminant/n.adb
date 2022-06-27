function N (X : Natural) return Integer
  with Pre => X < Integer'Last,
  Depends => (N'Result => X), Post => N'Result = X
is
   type T (D : Integer) is record
      C : Integer := D - 1;
   end record;

   type P is access T;

   --  Discriminant assignment via allocator; entire access
   --  variable effectively depends on discriminant.
   A : P := new T (X + 1);

begin
   pragma Assert (P'(new T (D => X + 1)) /= null);--@RESOURCE_LEAK:FAIL
   return A.C;
   --  Memory leak may happen, for this test we don't care.
end N;
