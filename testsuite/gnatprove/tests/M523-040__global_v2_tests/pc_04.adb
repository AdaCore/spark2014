with G;     use G;
with PC_01; use PC_01;
with PC_02; use PC_02;

package body PC_04 is
   procedure C_04 is
   begin
      if N > 0 then
         C_01;
      else
         C_02;
      end if;
   end C_04;
end PC_04;
