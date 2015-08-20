with Interfaces;
with Interfaces.C.Extensions;

with Ada.Numerics; use Ada.Numerics;

package Types
with SPARK_Mode
is

   --  General types used for C Interfacing.

   type T_Int8   is new Interfaces.Integer_8;
   type T_Int16  is new Interfaces.Integer_16;
   type T_Int32  is new Interfaces.Integer_32;
   type T_Uint8  is new Interfaces.Unsigned_8;
   type T_Uint16 is new Interfaces.Unsigned_16;
   type T_Uint32 is new Interfaces.Unsigned_32;

   subtype Natural_Float is Float range 0.0 .. Float'Last;

   --  Types used by the stabilization system

   --  Allowed delta time range.
   subtype T_Delta_Time   is Float range 0.002 .. 1.0;

   --  Smoothing terms. Used for barycentric expressions.
   subtype T_Alpha        is Float range 0.0 .. 1.0;

   --  Angle range type, in degrees.
   --  This range is deduced from the MPU9150 Datasheet.
   subtype T_Degrees        is Float range -360.0 .. 360.0;

   --  Allowed speed range, in m/s.
   --  This range is deduced from the MPU9150 Datasheet.
   subtype T_Speed        is Float range -2000.0 .. 2000.0;

   --  Allowed sensitivity for target altitude change in Alt Hold mode.
   subtype T_Sensitivity  is Float range 100.0 .. 300.0;

   --  Allowed factor to relate Altitude with Thrust command for motors.
   subtype T_Motor_Fac    is Float range 10_000.0 .. 15_000.0;

   --  Types used for the implementation of Mahony and Madgwick algorithms

   subtype T_Quaternion is Float range -1.0 .. 1.0;

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

end Types;
