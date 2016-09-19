with System.OS_Interface;

package Ada.Real_Time with
  SPARK_Mode
is

   pragma Assert (System.OS_Interface.Ticks_Per_Second >= 1);

end Ada.Real_Time;
