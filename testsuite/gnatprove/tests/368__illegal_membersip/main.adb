procedure Main with SPARK_Mode is
   type R is record
      F, G : Integer;
   end record;

   function "=" (X, Y : R) return Boolean is (X.F = Y.F) with SPARK_Mode => Off;

   function F (X, Y, Z : R) return Boolean is (X in Y | Z);

begin
   null;
end Main;
