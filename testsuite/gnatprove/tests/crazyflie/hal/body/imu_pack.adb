package body IMU_Pack is

   function IMU_6_Calibrated return Boolean is
      function IMU_6_Calibrated_Wrapper return Integer;
      pragma Import (C, IMU_6_Calibrated_Wrapper, "imu6IsCalibrated");
   begin
      return IMU_6_Calibrated_Wrapper /= 0;
   end IMU_6_Calibrated;


   function IMU_Has_Barometer return Boolean is
      function IMU_Has_Barometer_Wrapper return Integer;
      pragma Import (C, IMU_Has_Barometer_Wrapper, "imuHasBarometer");
   begin
      return IMU_Has_Barometer_Wrapper /= 0;
   end IMU_Has_Barometer;

end IMU_Pack;
