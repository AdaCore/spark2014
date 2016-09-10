package body Outer is

   task body TT is
   begin
      loop
         X := not X;
      end loop;
   end;

end;
