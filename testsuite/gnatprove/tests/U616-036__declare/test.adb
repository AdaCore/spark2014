procedure Test is

   function F (X : Integer) return Integer is (X)
   with Post =>
      (declare
         Res : constant Integer := F'Result;
       begin
         Res = X + 1 and then
         Res = X + 2);

   function G (X : Integer) return Integer is (X)
   with Post =>
      (declare
         Res : constant Integer := G'Result;
       begin
         Res = X and then
         Res = X + 2);

   function H (X : Integer) return Integer is (X)
   with Post =>
      (declare
         Res : constant Integer := H'Result;
       begin
         Res = X);
begin
   null;
end Test;
