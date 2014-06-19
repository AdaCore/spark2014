with G;     use G;
with PR_05; use PR_05;

package body PR_04 is
   procedure R_04 (A : Integer) is
   begin
      if A > 0 then
         X := 0;
      else
         R_05 (A);
      end if;
   end R_04;
end PR_04;
