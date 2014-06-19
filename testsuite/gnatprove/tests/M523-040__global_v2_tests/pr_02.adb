with G;     use G;
with PR_03; use PR_03;

package body PR_02 is
   procedure R_02 is
   begin
      X := X - 1;
      Y := X;
      if Y > 0 then
         R_03;
      else
         Z := 1;
         W := 0;
      end if;
   end R_02;
end PR_02;
