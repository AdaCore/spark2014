package body Q is

   task body Outsider is
   begin
      loop
         P.Flip;
      end loop;
   end;

end;
