package body Bar with SPARK_Mode is
   procedure Inc (Int : in out Integer) is
      --Int : Integer renames C.F.all;
   begin
      Int := Int + 1;
   end Inc;

   function Get return Integer is
   begin
      return C.F.all;
   end;
begin
   Inc (C.F.all);
end Bar;
