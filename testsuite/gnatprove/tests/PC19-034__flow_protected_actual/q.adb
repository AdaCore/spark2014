with P;

package body Q is

   task body TT is
   begin
      loop
         P.Flip (P.PO1);
      end loop;
   end;
      
end;
