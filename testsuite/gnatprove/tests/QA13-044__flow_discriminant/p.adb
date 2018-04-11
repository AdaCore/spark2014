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

   function Boo (Input : Integer) return T
   is
      type Proxy is new T (Input);

      Result : Proxy;
   begin
      return T (Result);
   end Boo;

   function Baz (Input : Integer) return Boolean
   is
      type Proxy is new T (Input);

      Result : Proxy;
   begin
      return Result.Discr > 3;
   end Baz;

   procedure Proc (Input : T)
   is
      type Proxy is new T (Input.Discr);

      O : Proxy;
      J : Integer := Input.Discr;

      procedure Nested
        with Global => (Input => (O, J)),
             Pre    => (J = O.Discr)
      is
         Loc : Proxy;
      begin
         Loc := O;
      end Nested;
   begin
      null;
   end Proc;
end P;
