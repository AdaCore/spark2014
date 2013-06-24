package Nested_Pkg
  with Abstract_State => Foobar
is
   pragma Elaborate_Body (Nested_Pkg);
   pragma SPARK_Mode (On);
end Nested_Pkg;
