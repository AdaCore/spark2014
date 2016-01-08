package body Q is

begin

   declare
      X     : aliased Integer;
      X_Ptr : access Integer := X'Access;
   begin
      X_Ptr.all := 0;
   end;
end;
