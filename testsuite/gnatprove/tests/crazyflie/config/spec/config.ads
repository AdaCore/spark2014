package Config is

   --  Constants used to configure the drone firmware

   --  Crazyflie 2.0 has an SMTM32F4 board
   STM32F4XX : constant Boolean := True;

   QUAD_FORMATION_X : constant Boolean := True;

   --  Two implemented algorithms for quaternions
   type Quaternion_Algorithm is (MAHONY, MADGWICK);
   SENSOR_FUSION_ALGORITHM : constant Quaternion_Algorithm := MAHONY;

end Config;
