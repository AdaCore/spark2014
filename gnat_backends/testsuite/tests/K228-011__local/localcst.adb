package body LocalCst is

   X : constant Integer := 1000;

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

   function Glob return Integer
   is
   begin
      return X;
   end Glob;
end LocalCst;
