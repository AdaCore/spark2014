package body Pack is

   procedure Set is
      procedure Sub (R : in out Boolean) is
      begin
         R := not R;
      end Sub;
   begin
      Sub (X.all);
   end Set;

   function Get return Boolean is
      function Sub (R : Boolean) return Boolean is
      begin
         return R;
      end Sub;
   begin
      return Sub (X.all);
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
