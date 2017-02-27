with GNAT.OS_Lib;

package P
  with SPARK_Mode => On
is

   type OS_Time is private;

private
   pragma SPARK_Mode(Off);

   type OS_Time is new GNAT.OS_Lib.OS_Time;

end;
