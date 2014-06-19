with G;     use G;
with PR_04; use PR_04;

package body PR_05 is
   procedure R_05 (A : Integer) is
   begin
      if A <= 0 then
         X := 0;
      else
         R_04 (A);
      end if;
   end R_05;
end PR_05;
