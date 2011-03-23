package body Pack is

   function F1 return Boolean is
   begin
      X := True;
      return X;
   end F1;

   function F2 return Boolean is
   begin
      return F1;
   end F2;

end;
