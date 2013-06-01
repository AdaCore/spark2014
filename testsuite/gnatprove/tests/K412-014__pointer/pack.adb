package body Pack is

   procedure Set is
   begin
      X.all := not X.all;
   end Set;

   function Get return Boolean is
   begin
      return X.all;
   end Get;

   procedure Test is
      A : Boolean := Get;
      B : Boolean;
   begin
      Set;
      B := Get;
      pragma Assert (A = B);
   end Test;

end;
