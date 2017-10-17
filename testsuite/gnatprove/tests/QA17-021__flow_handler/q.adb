with P;

package body Q is

   protected body PO3 is
      procedure Proc is
      begin
         P.X := not P.X;
      end;
   end;

end;
