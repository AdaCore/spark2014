with G;     use G;
with PR_02; use PR_02;

package body PR_03 is
   procedure R_03 is
   begin
      W := 1;
      if Y < 0 then
         X := X + 10;
         R_02;
      else
         Z := 0;
      end if;
   end R_03;
end PR_03;
