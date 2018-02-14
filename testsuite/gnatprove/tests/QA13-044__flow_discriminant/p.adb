package body P is

   function Foo (Input : Integer) return T
   is
      Proxy : T (Input);
      Result : constant T (Input) := Proxy;
   begin
      return Result;
   end Foo;

   function Bar (Input : Integer) return T
   is
      Result : T (Input);
   begin
      return Result;
   end Bar;

   function Bla (Input : Integer) return T
   is
      type Proxy is record
         C : T (Input);
      end record;

      Result : Proxy;
   begin
      return Result.C;
   end Bla;

end P;
