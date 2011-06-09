procedure Arrays is
   type Idx is range 0 .. 10;
   type A is array (Idx) of Idx;
   type B is array (Idx) of A;

   Obj : B;
begin
   Obj(1)(1) := 1;
   pragma Assert (Obj(1)(1) = 1);
end;
