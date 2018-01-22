with P;
package body T is
   task body TT is
   begin
      while True loop
         P;
      end loop;
   end;
end T;
