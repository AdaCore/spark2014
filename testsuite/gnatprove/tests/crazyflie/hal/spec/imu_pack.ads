with Ada.Numerics; use Ada.Numerics;

package IMU_Pack
with SPARK_Mode
is

   --  Types

   --  These ranges are deduced from the MPU9150 specification.
   --  It corresponds to the maximum range of values that can be output
   --  by the IMU.

   --  Type for angular speed output from gyro, degrees/s
   subtype T_Rate is Float range -3_000.0  .. 3_000.0;
   --  Type for angular speed output from gyro, rad/s
   subtype T_Rate_Rad
     is Float range -3_000.0 * Pi / 180.0 .. 3_000.0 * Pi / 180.0;
   --  Type for acceleration output from accelerometer, in G
   subtype T_Acc  is Float range -16.0 .. 16.0;
   --  Type for magnetometer output, in micro-Teslas
   subtype T_Mag  is Float range -1_200.0  .. 1_200.0;

   --  Type used to ensure that accelation normalization can't lead to a
   --  division by zero in SensFusion6_Pack algorithms
   MIN_NON_ZERO_ACC : constant := 2.0 ** (-74);

   subtype T_Acc_Lifted is T_Acc with
       Static_Predicate => T_Acc_Lifted = 0.0 or else
     T_Acc_Lifted <= -MIN_NON_ZERO_ACC or else
     T_Acc_Lifted >= MIN_NON_ZERO_ACC;

   --  Type used when we want to collect several accelerometer samples.
   type T_Acc_Array is array (Integer range <>) of T_Acc;

   type Gyroscope_Data is record
      X : T_Rate;
      Y : T_Rate;
      Z : T_Rate;
   end record;

   type Accelerometer_Data is record
      X : T_Acc;
      Y : T_Acc;
      Z : T_Acc;
   end record;

   type Magnetometer_Data is record
      X : T_Mag;
      Y : T_Mag;
      Z : T_Mag;
   end record;

   pragma Convention (C, Gyroscope_Data);
   pragma Convention (C, Accelerometer_Data);
   pragma Convention (C, Magnetometer_Data);

   --  Constants

   IMU_UPDATE_FREQ : constant := 500.0;
   IMU_UPDATE_DT   : constant := 1.0 / IMU_UPDATE_FREQ;

   --  Procedures and functions

   procedure IMU_9_Read
     (Gyro : in out Gyroscope_Data;
      Acc  : in out Accelerometer_Data;
      Mag  : in out Magnetometer_Data)
     with
       Global => null;

   pragma Import (C, IMU_9_Read, "imu9Read");

   function IMU_6_Calibrated return Boolean;

   function IMU_Has_Barometer return Boolean;

end IMU_Pack;
