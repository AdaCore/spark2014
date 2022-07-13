procedure Main is

   function F (X : in out Integer) return Integer;

   function F (X : in out Integer) return Integer is
   begin
      X := X + 1;
      return X;
   end F;

begin
   null;
end Main;
