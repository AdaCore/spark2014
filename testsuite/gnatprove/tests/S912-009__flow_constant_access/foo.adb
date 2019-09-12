package body Foo with SPARK_Mode is
   procedure Inc is
      Int : Integer renames C.F.all;
   begin
      Int := Int + 1;
   end Inc;

   function Get return Integer is
   begin
      return C.F.all;
   end;
end Foo;
