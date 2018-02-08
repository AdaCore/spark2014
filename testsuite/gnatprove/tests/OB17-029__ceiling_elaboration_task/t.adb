with P;
package body T is
   task body TT is
   begin
      while True loop
         P (0);
      end loop;
   end;
end T;
