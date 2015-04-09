package IMU_Pack
with SPARK_Mode
is

   --  Types

   subtype T_Acc  is Float range -16.0 .. 16.0;

   MIN_NON_ZERO_ACC : constant := 2.0 ** (-74);

   subtype T_Acc_Lifted is T_Acc with
     Static_Predicate => T_Acc_Lifted = 0.0 or else
     T_Acc_Lifted not in -MIN_NON_ZERO_ACC .. MIN_NON_ZERO_ACC;

end IMU_Pack;
