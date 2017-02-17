package body Glob is
   procedure Sub is
   begin
      G := True;
   end;

   procedure P is
   begin
      Sub;
   end P;
end;
