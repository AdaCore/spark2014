package Q is

   type T (D : Integer) is null record;

   Obj : T (D => 0);

   type TT is record
      Component: T (D => 0);
   end record;

   Nested : TT;

   type T2 is record
      C1 : Integer := Obj.D;               --  NOK
      C2 : Integer := Nested.Component.D;  --  NOK
   end record;

end;
