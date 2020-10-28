package body P is
   procedure Explicit is
   begin
      X := not X;
   end;

   procedure Implicit is
   begin
      X := not X;
   end;
end;
