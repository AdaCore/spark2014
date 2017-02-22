package P is

   type T (D : Integer) is null record;

   Obj : T (D => 0);

   type TT is record
      Component: T (D => 0);
   end record;

   Nested : TT;

   function Proxy1 return Integer is (Obj.D) with Pre => True;
   function Proxy2 return Integer is (Nested.Component.D) with Pre => True;

   type T2 is record
      C1 : Integer := Proxy1;  --  NOK
      C2 : Integer := Proxy2;  --  NOK
   end record;

end;
