package body S is

   procedure Not_Zero (E : Element) is
   begin
      if E = 0 then
         raise Program_Error;
      end if;
   end Not_Zero;

end S;
