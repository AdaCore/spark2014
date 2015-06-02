package P
  with SPARK_Mode => On
is
   pragma Elaborate_Body;
private
  with SPARK_Mode => Off
   Dummy : constant := 0;
end P;
