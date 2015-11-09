package body P is

   task body T1 is
      Counter : Natural := 5;
   begin
      loop
         pragma Loop_Invariant (Counter in 0 .. 5); --  precise loop invariant
         if Counter /= 0 then
            Counter := Counter - 1;
         end if;
      end loop;
   end;

   task body T2 is
      Counter : Natural := 5;
   begin
      loop
         pragma Loop_Invariant (Counter >= 0); --  imprecise loop invariant
         if Counter /= 0 then
            Counter := Counter - 1;
         end if;
      end loop;
   end;

   task body T3 is
      Counter : Natural := 5;
   begin
      loop
         --  no loop invariant
         if Counter /= 0 then
            Counter := Counter - 1;
         end if;
      end loop;
   end;

end;
