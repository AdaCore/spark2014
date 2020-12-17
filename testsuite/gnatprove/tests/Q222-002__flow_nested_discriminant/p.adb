procedure P with Global => null is

   type T (D : Integer) is null record;

   type TT (D : Integer) is record
      Component : T (D => D);
   end record;

   procedure P (X : in out T) with Pre => True is
      function Proxy1 return Integer is (X.D) with Pre => True;

      type T2 is record
         C1 : Integer := Proxy1;  --  NOK
      end record;
   begin
      null;
   end P;

   procedure Q (X : in out TT) with Pre => True is
      function Proxy2 return Integer is (X.Component.D) with Pre => True;

      type T2 is record
         C1 : Integer := Proxy2;  --  NOK
      end record;
   begin
      null;
   end Q;
begin
   null;
end P;
