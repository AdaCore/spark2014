package Pkg_A
  with Initializes => (X, Z)
is
   pragma Elaborate_Body (Pkg_A);
   pragma SPARK_Mode (On);

   X : Integer;
   Y : Integer;
   Z : Integer := 12345;  --  "I have the same combination on my suitcase"

end Pkg_A;
