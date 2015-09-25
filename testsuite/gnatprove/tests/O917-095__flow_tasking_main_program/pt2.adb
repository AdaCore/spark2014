with P;

package body PT2 is
   task body T is
   begin
      loop
         P.X := not P.X;
      end loop;
   end;
end;
