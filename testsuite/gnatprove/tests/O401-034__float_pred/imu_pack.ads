package IMU_Pack
with SPARK_Mode
is

   --  Types

   --  These ranges are deduced from the MPU9150 specification.
   --  It corresponds to the maximum range of values that can be output
   --  by the IMU.
   subtype T_Rate is Float range -3_000.0  .. 3_000.0;
   subtype T_Acc  is Float range -16.0 .. 16.0;
   subtype T_Mag  is Float range -4_800.0  .. 4_800.0;

   MIN_NON_ZERO_ACC : constant := 2.0 ** (-74);

   subtype T_Acc_Lifted is T_Acc with
       Static_Predicate => T_Acc_Lifted = 0.0 or else
       T_Acc_Lifted not in -MIN_NON_ZERO_ACC .. MIN_NON_ZERO_ACC;

end IMU_Pack;
