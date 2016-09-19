with System.OS_Interface;
pragma Elaborate_All (System.OS_Interface);

package Ada.Real_Time with
  SPARK_Mode,
  Abstract_State => (Clock_Time with Synchronous,
                                     External => (Async_Readers,
                                                  Async_Writers)),
  Initializes    => Clock_Time
is
   pragma Assert
     (System.OS_Interface.Ticks_Per_Second >= 50_000,
      "Ada RM D.8 (30) requires " &
      "that Time_Unit shall be less than or equal to 20 microseconds");

   procedure P;

private
   pragma SPARK_Mode (Off);

end Ada.Real_Time;
