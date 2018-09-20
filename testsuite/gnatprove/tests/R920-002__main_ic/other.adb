with Main;
with Pack;

package body Other is
   procedure P1 is
   begin
      Main; --@PRECONDITION:FAIL
   end P1;

   procedure P2 is
   begin
      Pack.I := 6;
      Main;
   end P2;
end Other;
