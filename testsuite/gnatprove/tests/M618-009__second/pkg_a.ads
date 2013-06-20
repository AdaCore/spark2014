package Pkg_A
  with Initializes => X
is
   pragma SPARK_Mode (On);

   X : Integer;
   Y : Integer;

   function Do_Something (X : Integer) return Integer
     with Pre => X in -100 .. 100;

end Pkg_A;
