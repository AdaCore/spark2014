package P is

   type T (Discr : Integer) is null record;

   function Foo (Input : Integer) return T
   with Depends => (Foo'Result => Input);

end P;
