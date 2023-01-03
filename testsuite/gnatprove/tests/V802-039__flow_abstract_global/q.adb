package body Q is

   procedure A (X : TT) is
   begin
      pragma Assert (X.CC = Y);
   end;

   procedure B (X : TT) is
   begin
      pragma Assert (X.CC = Y);
   end;

end;
