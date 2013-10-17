pragma SPARK_Mode (On);

package body Sat is

   function Add (X , Y : My_Int) return My_Int is
     (if X + Y < 10_000 then
         X + Y
       else
         10_000);

   function Mult (X , Y : My_Int) return My_Int is
     (if X * Y < 10_000 then
         X * Y
       else
         10_000);

end Sat;
