with P;

package body Test1 is

   task body TT1 is
   begin
      loop
         P.PO1.E1;
      end loop;
   end;

   task body TT2 is
   begin
      loop
         P.PO1.E2;
      end loop;
   end;

end;
