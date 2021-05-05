package body P
with SPARK_Mode => On
is
   procedure A (X : T) is
   begin
      X.all := 10; --  We should have an error here, A should not modify X
   end A;

   procedure B (X : S) is
   begin
      X.all := 10;
      C.all := 10; --  We should have an error here, C is a constant
      D.all := 10;
   end B;

   procedure F (X : T) renames B; --  We should have an error here, B can modify X

   procedure G (X : U) is
   begin
      X.all := 10; --  We should have an error here, G should not modify X
   end G;
end P;
