pragma Extensions_Allowed (All_Extensions);
procedure Main with SPARK_Mode is
   Y : Integer;
   X : Integer;
   function Test (I : Integer) return Boolean with Import, Global => null;
begin
   for I in 1 .. 100 loop
      continue when Test (I);
      Y := 0;
   end loop;
   X := Y; -- Y might not be initialized
   for J in 1 .. 100 loop
      continue when Test (Y); -- Y might not be initialized
      Y := X;
   end loop;
   for K in 1 .. 100 loop
      continue when test (X); -- continue condition is stable
      Y := X;
   end loop;
   Outer: for L in 1 .. 100 loop
      for M in 1 .. 100 loop
         continue Outer when Test  (M);
         Y := M;
      end loop;
      Y := L;
   end loop Outer;
   X := Y; -- Y might not be initialized
   if Test (152) then
      Outer2 : for A in 1 .. 100 loop
         Medium2 : for B in 1 .. 100 loop
            Inner2 : for C in 1 .. 100 loop
               continue Medium2 when Test (C);
            end loop Inner2;
         end loop Medium2;
         Y := A;
      end loop Outer2;
   else
      Outer3 : for A in 1 .. 100 loop
         Medium3 : for B in 1 .. 100 loop
            Inner3 : for C in 1 .. 100 loop
               Y := C;
               continue Medium3 when Test (C);
            end loop Inner3;
         end loop Medium3;
      end loop Outer3;
   end if;
   X := Y; -- Y is initialized
end Main;
