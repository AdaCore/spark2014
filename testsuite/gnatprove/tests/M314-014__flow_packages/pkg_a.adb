package body Pkg_A
is
   pragma SPARK_Mode (On);

   function Do_Something (X : Integer) return Integer is (X * 2)
     with Pre => X in -100 .. 100;

begin

   Y := Do_Something (X);

end Pkg_A;
