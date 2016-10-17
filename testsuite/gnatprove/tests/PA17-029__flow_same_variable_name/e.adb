with P;

package body E is

   procedure Unused is begin null; end;

begin
   declare
      X : Integer := P.X;
   begin
      null;
   end;
end;
