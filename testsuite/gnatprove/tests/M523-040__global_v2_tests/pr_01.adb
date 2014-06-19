with G;     use G;

package body PR_01 is
   procedure R_01 is
   begin
      Y := N;
      if N <= 0 then
         return;
      end if;
      N := N - 1;
      X := N;
      R_01;
   end R_01;
end PR_01;
