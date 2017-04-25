package body Indirect is

   procedure Proc is
   begin
      null;
   end Proc;

begin
   X := P.P;
   pragma Assert (X);
end Indirect;
