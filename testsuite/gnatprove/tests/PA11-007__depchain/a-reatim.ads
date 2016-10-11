with System.OS_Interface;

package Ada.Real_Time with
  SPARK_Mode
is
   pragma Assert
     (System.OS_Interface.Ticks_Per_Second >= 50_000,
      "Ada RM D.8 (30) requires " &
      "that Time_Unit shall be less than or equal to 20 microseconds");

   procedure P;

end Ada.Real_Time;
