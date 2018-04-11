package P is

   type T (Discr : Integer) is null record;

   function Foo (Input : Integer) return T
     with Depends => (Foo'Result => Input);

   function Bar (Input : Integer) return T
     with Depends => (Bar'Result => Input);

   function Bla (Input : Integer) return T
     with Depends => (Bla'Result => Input);

   function Boo (Input : Integer) return T
     with Depends => (Boo'Result => Input);

   function Baz (Input : Integer) return Boolean
     with Depends => (Baz'Result => Input);

   procedure Proc (Input : T);

end P;
