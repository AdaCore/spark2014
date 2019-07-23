package body Q is
   task body TT is
   begin
      loop
         P.Flip;
      end loop;
   end TT;

   TO : TT;
end Q;
