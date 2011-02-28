package body LocalCst is

   function Cst return Integer
   is
      X : constant Integer := 5000;
   begin
      return X;
   end Cst;

   function Id (N : Integer) return Integer
   is
      X : constant Integer := N;
   begin
      return X;
   end Id;
end LocalCst;
