package body P is
   procedure Reset is
   begin
      X := False;
   end;

   function Get return Boolean is
   begin
      return X;
   end;
end;
