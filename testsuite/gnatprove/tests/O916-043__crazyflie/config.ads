with Ada.Real_Time; use Ada.Real_Time;
with System;
with Types; use Types;
with MPU9250_Pack; use MPU9250_Pack;

package Config is

   --  Constants used to configure the drone firmware

   --  Crazyflie 2.0 has an SMTM32F4 board
   STM32F4XX : constant Boolean := True;
   QUAD_FORMATION_X : constant Boolean := True;
   CPU_CLOCK_HZ : constant T_Uint32 := 168000000;
   TICK_RATE_HZ : constant T_Uint16 := 1000;
   TICK_RATE_MS : constant T_Uint16 := 1000 / TICK_RATE_HZ;

   --  Task priorities
   MAIN_TASK_PRIORITY      : constant System.Priority := 4;
   CRTP_RXTX_TASK_PRIORITY : constant System.Priority := 2;
   SYSLINK_TASK_PRIORITY   : constant System.Priority := 3;
   LOG_TASK_PRIORITY       : constant System.Priority := 1;
   PM_TASK_PRIORITY        : constant System.Priority := 0;

   --  Two implemented algorithms for quaternions
   type Quaternion_Algorithm is (MAHONY, MADGWICK);
   SENSOR_FUSION_ALGORITHM : constant Quaternion_Algorithm := MAHONY;

   --  Link layers implemented to communicate via the CRTP protocol
   type Link_Layer is (RADIO_LINK, USB_LINK, ESKY_LINK);
   LINK_LAYER_TYPE : constant Link_Layer := RADIO_LINK;

   PORT_MAX_DELAY : constant T_Uint16 := T_Uint16'Last;

   PORT_MAX_DELAY_TIME_MS : constant Time_Span
     := Milliseconds (Integer (PORT_MAX_DELAY / TICK_RATE_MS));

   --  Radio configuration
   RADIO_CHANNEL       : constant := 80;
   RADIO_DATARATE      : constant := 0;

   --  IMU configuration
   IMU_GYRO_FS_CONFIG  : constant MPU9250_FS_Gyro_Range
     := MPU9250_Gyro_FS_2000;
   IMU_ACCEL_FS_CONFIG : constant MPU9250_FS_Accel_Range
     := MPU9250_Accel_FS_8;

end Config;
