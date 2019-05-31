function F (A, B : Integer) return Integer
  with Post    => F'Result = B,
       Depends => (F'Result => B, null => A)
is
   type T is array (Integer range <>, Integer range <>) of Boolean;
   X : T (1 .. A, 1 .. B);
begin
   return X'Last (2);
end F;
