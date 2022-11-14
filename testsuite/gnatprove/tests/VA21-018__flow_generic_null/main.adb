procedure Main is
   generic
      type E is private;
      with procedure P (X : E) is null;
   package G is
      procedure Use_P (X : E);
   end G;
   package body G is
      procedure Use_P (X : E) is
      begin
         P (X);
      end Use_P;
   end G;
   procedure P1 (I : Integer) is null;
   package I is new G (Integer, P => P1);
begin
   I.Use_P (1);
end Main;
