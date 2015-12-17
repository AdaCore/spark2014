package P with
  SPARK_Mode => On
is

   function Zero return Integer is (0);

   pragma Assert (Zero /= 0);

private
   pragma SPARK_Mode (Off);
end;
