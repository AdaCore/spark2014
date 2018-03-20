with Maths_Pack; use Maths_Pack;
with Safety_Pack; use Safety_Pack;
with Config; use Config;
with Ada.Numerics; use Ada.Numerics;
with Interfaces.C; use Interfaces.C;

package body SensFusion6_Pack
with SPARK_Mode,
  Refined_State => (SensFusion6_State => (Is_Init,
                                          Q0,
                                          Q1,
                                          Q2,
                                          Q3,
                                          Two_Kp,
                                          Two_Ki,
                                          Integral_FBx,
                                          Integral_FBy,
                                          Integral_FBz,
                                          Beta))
is procedure Madgwick_Update_Q (Gx : T_Rate; Gy : T_Rate; Gz : T_Rate; Ax : T_Acc; Ay : T_Acc; Az : T_Acc; Dt : T_Delta_Time);
   procedure Mahony_Update_Q (Gx : T_Rate; Gy : T_Rate; Gz : T_Rate; Ax : T_Acc; Ay : T_Acc; Az : T_Acc; Dt : T_Delta_Time);
   procedure SensFusion6_Init is
   begin
      if Is_Init = True then
         return;
      end if;

      Is_Init := True;
   end SensFusion6_Init;

   function SensFusion6_Test return bool is
   begin
      return Is_Init;
   end SensFusion6_Test;

   procedure Madgwick_Update_Q
     (Gx : T_Rate;
      Gy : T_Rate;
      Gz : T_Rate;
      Ax : T_Acc;
      Ay : T_Acc;
      Az : T_Acc;
      Dt : T_Delta_Time)
   is
      Recip_Norm    : Float;
      S0            : Float;
      S1            : Float;
      S2            : Float;
      S3            : Float;
      Q_Dot1        : Float;
      Q_Dot2        : Float;
      Q_Dot3        : Float;
      Q_Dot4        : Float;
      Q0_X2         : Float;
      Q1_X2         : Float;
      Q2_X2         : Float;
      Q3_X2         : Float;
      Q0_X4         : Float;
      Q1_X4         : Float;
      Q2_X4         : Float;
      Q1_X8         : Float;
      Q2_X8         : Float;
      Q0_Q0         : Float;
      Q1_Q1         : Float;
      Q2_Q2         : Float;
      Q3_Q3         : Float;
      Norm_Ax       : T_Acc;
      Norm_Ay       : T_Acc;
      Norm_Az       : T_Acc;
      Q0_Tmp        : Float;
      Q1_Tmp        : Float;
      Q2_Tmp        : Float;
      Q3_Tmp        : Float;
      Ax_Tmp        : T_Acc_Lifted;
      Ay_Tmp        : T_Acc_Lifted;
      Az_Tmp        : T_Acc_Lifted;
      Square_Sum    : Natural_Float;
   begin
      --  Rate of change of quaternion from gyroscope
      Q_Dot1 := 0.5 * (-Q1 * Gx - Q2 * Gy - Q3 * Gz);
      Q_Dot2 := 0.5 * (Q0 * Gx + Q2 * Gz - Q3 * Gy);
      Q_Dot3 := 0.5 * (Q0 * Gy - Q1 * Gz + Q3 * Gx);
      Q_Dot4 := 0.5 * (Q0 * Gz + Q1 * Gy - Q2 * Gx);

      --  Compute feedback only if accelerometer measurement valid
      --  (avoids NaN in accelerometer normalisation)
      if (not ((Ax = 0.0) and (Ay = 0.0) and (Az = 0.0))) then
         --  Normalize accelerometer measurement
         Ax_Tmp := Lift_Away_From_Zero (Ax);
         Ay_Tmp := Lift_Away_From_Zero (Ay);
         Az_Tmp := Lift_Away_From_Zero (Az);
         Square_Sum := Ax_Tmp * Ax_Tmp + Ay_Tmp * Ay_Tmp + Az_Tmp * Az_Tmp;
         Recip_Norm := Inv_Sqrt (Square_Sum);
         Norm_Ax := Saturate (Ax * Recip_Norm, -1.0, 1.0);
         Norm_Ay := Saturate (Ay * Recip_Norm, -1.0, 1.0);
         Norm_Az := Saturate (Az * Recip_Norm, -1.0, 1.0);

         --  Auxiliary variables to avoid repeated arithmetic
         Q0_X2 := 2.0 * Q0;
         Q1_X2 := 2.0 * Q1;
         Q2_X2 := 2.0 * Q2;
         Q3_X2 := 2.0 * Q3;
         Q0_X4 := 4.0 * Q0;
         Q1_X4 := 4.0 * Q1;
         Q2_X4 := 4.0 * Q2;
         Q1_X8 := 8.0 * Q1;
         Q2_X8 := 8.0 * Q2;
         Q0_Q0 := Q0 * Q0;
         Q1_Q1 := Q1 * Q0;
         Q2_Q2 := Q2 * Q0;
         Q3_Q3 := Q3 * Q0;

         --  Gradient decent algorithm corrective step
         S0 := Q0_X4 * Q2_Q2 + Q2_X2 * Norm_Ax +
           Q0_X4 * Q1_Q1 - Q1_X2 * Norm_Ay;
         S1 := Q1_X4 * Q3_Q3 - Q3_X2 * Norm_Ax + 4.0 * Q0_Q0 * Q1 -
           Q0_X2 * Norm_Ay - Q1_X4 + Q1_X8 * Q1_Q1 +
             Q1_X8 * Q2_Q2 + Q1_X4 * Norm_Az;
         S2 := 4.0 * Q0_Q0 * Q2 + Q0_X2 * Norm_Ax + Q2_X4 * Q3_Q3 -
           Q3_X2 * Norm_Ay - Q2_X4 + Q2_X8 * Q1_Q1 +
             Q2_X8 * Q2_Q2 + Q2_X4 * Norm_Az;
         S3 := 4.0 * Q1_Q1 * Q3 - Q1_X2 * Norm_Ax +
           4.0 * Q2_Q2 * Q3 - Q2_X2 * Norm_Ay;

         --  Normalize step magnitudes
         Recip_Norm := Inv_Sqrt (S0 * S0 + S1 * S1 + S2 * S2 + S3 * S3);
         S0 := S0 * Recip_Norm;
         S1 := S1 * Recip_Norm;
         S2 := S2 * Recip_Norm;
         S3 := S3 * Recip_Norm;

         --  Apply feedback step
         Q_Dot1 := Q_Dot1 - Beta * S0;
         Q_Dot2 := Q_Dot2 - Beta * S1;
         Q_Dot3 := Q_Dot3 - Beta * S2;
         Q_Dot4 := Q_Dot4 - Beta * S3;
      end if;

      --  Integrate rate of change of quaternion to yield quatrenion
      Q0_Tmp := Q0 + Q_Dot1 * Dt;
      Q1_Tmp := Q1 + Q_Dot2 * Dt;
      Q2_Tmp := Q2 + Q_Dot3 * Dt;
      Q3_Tmp := Q3 + Q_Dot4 * Dt;

      --  Normalize quaternion
      Recip_Norm := Inv_Sqrt
        (Q0_Tmp * Q0_Tmp + Q1_Tmp * Q1_Tmp +
           Q2_Tmp * Q2_Tmp + Q3_Tmp * Q3_Tmp);
      Q0 := Saturate
        (Q0_Tmp * Recip_Norm, T_Quaternion'First, T_Quaternion'Last);
      Q1 := Saturate
        (Q1_Tmp * Recip_Norm, T_Quaternion'First, T_Quaternion'Last);
      Q2 := Saturate
        (Q2_Tmp * Recip_Norm, T_Quaternion'First, T_Quaternion'Last);
      Q3 := Saturate
        (Q3_Tmp * Recip_Norm, T_Quaternion'First, T_Quaternion'Last);
   end Madgwick_Update_Q;

   --  Subtypes used to help SPARK proving absence of runtime errors
   --  in the Mahony algorithm

   subtype T_Norm_Acc is T_Acc range -1.0 .. 1.0;
   subtype T_Float_1  is Float range -3.0 .. 3.0;
   subtype T_Float_2  is Float range -7.0 .. 7.0;
   subtype T_Float_3  is
     Float range -4.0 * MAX_RATE_CHANGE .. 4.0 * MAX_RATE_CHANGE;
   subtype T_Float_4  is Float range -MAX_RATE_CHANGE .. MAX_RATE_CHANGE;
   subtype T_Float_5  is Float range T_Rate_Rad'First - MAX_INTEGRAL_ERROR
     .. T_Rate_Rad'Last + MAX_INTEGRAL_ERROR;

   procedure Mahony_Update_Q
     (Gx : T_Rate;
      Gy : T_Rate;
      Gz : T_Rate;
      Ax : T_Acc;
      Ay : T_Acc;
      Az : T_Acc;
      Dt : T_Delta_Time) is
      Recip_Norm      : Float;
      Norm_Ax         : T_Norm_Acc;
      Norm_Ay         : T_Norm_Acc;
      Norm_Az         : T_Norm_Acc;
      --  Conversion from degrees/s to rad/s
      Rad_Gx          : constant T_Rate_Rad := Gx * Pi / 180.0;
      Rad_Gy          : constant T_Rate_Rad := Gy * Pi / 180.0;
      Rad_Gz          : constant T_Rate_Rad := Gz * Pi / 180.0;
      --  Estimated direction of gravity and vector perpendicular
      --  to magnetic flux
      Half_Vx         : constant T_Float_1 := Q1 * Q3 - Q0 * Q2;
      Half_Vy         : constant T_Float_1 := Q0 * Q1 + Q2 * Q3;
      Half_Vz         : constant T_Float_1 := Q0 * Q0 - 0.5 + Q3 * Q3;
      Half_Ex         : T_Float_2;
      Half_Ey         : T_Float_2;
      Half_Ez         : T_Float_2;
      Q0_Tmp          : T_Float_3;
      Q1_Tmp          : T_Float_3;
      Q2_Tmp          : T_Float_3;
      Q3_Tmp          : T_Float_3;
      Qa              : constant T_Quaternion := Q0;
      Qb              : constant T_Quaternion := Q1;
      Qc              : constant T_Quaternion := Q2;
      Ax_Lifted       : T_Acc_Lifted;
      Ay_Lifted       : T_Acc_Lifted;
      Az_Lifted       : T_Acc_Lifted;
      Square_Sum      : Natural_Float;
      Rate_Change_Gx  : T_Float_4 := Rad_Gx;
      Rate_Change_Gy  : T_Float_4 := Rad_Gy;
      Rate_Change_Gz  : T_Float_4 := Rad_Gy;
      Integ_FB_Gx     : T_Float_5 := Rad_Gx;
      Integ_FB_Gy     : T_Float_5 := Rad_Gy;
      Integ_FB_Gz     : T_Float_5 := Rad_Gz;
   begin
      if (not ((Ax = 0.0) and (Ay = 0.0) and (Az = 0.0))) then
         --  Normalize accelerometer measurement
         Ax_Lifted := Lift_Away_From_Zero (Ax);
         Ay_Lifted := Lift_Away_From_Zero (Ay);
         Az_Lifted := Lift_Away_From_Zero (Az);
         Square_Sum := Ax_Lifted * Ax_Lifted +
           Ay_Lifted * Ay_Lifted + Az_Lifted * Az_Lifted;
         --  We ensured that Ax_Tmp, Ay_Tmp, Az_Tmp are sufficiently far away
         --  from zero with 'Lift_Away_From_Zero' function
         --  so that the Square_Sum calculation results in a value
         --  diferent from 0.0 and positive.
         Recip_Norm := Inv_Sqrt (Square_Sum);
         --  These asserts are only needed to help SPARK
         pragma Assert (Recip_Norm in 0.0 .. 2.7E+22);
         pragma Assert (Ax in -16.0 .. 16.0);
         pragma Assert (Ay in -16.0 .. 16.0);
         pragma Assert (Az in -16.0 .. 16.0);
         Norm_Ax := Saturate (Ax * Recip_Norm, -1.0, 1.0);
         Norm_Ay := Saturate (Ay * Recip_Norm, -1.0, 1.0);
         Norm_Az := Saturate (Az * Recip_Norm, -1.0, 1.0);

         --  Error is sum of cross product between estimated
         --  and measured direction of gravity
         Half_Ex := (Norm_Ay * Half_Vz - Norm_Az * Half_Vy);
         Half_Ey := (Norm_Az * Half_Vx - Norm_Ax * Half_Vz);
         Half_Ez := (Norm_Ax * Half_Vy - Norm_Ay * Half_Vx);

         --  Compute and apply integral feedback if enabled
         if Two_Ki > 0.0 then
            Integral_FBx := Saturate (Integral_FBx + Two_Ki * Half_Ex * Dt,
                                      -MAX_INTEGRAL_ERROR,
                                      MAX_INTEGRAL_ERROR);
            Integral_FBy := Saturate (Integral_FBy + Two_Ki * Half_Ey * Dt,
                                      -MAX_INTEGRAL_ERROR,
                                      MAX_INTEGRAL_ERROR);
            Integral_FBz := Saturate (Integral_FBz + Two_Ki * Half_Ez * Dt,
                                      -MAX_INTEGRAL_ERROR,
                                      MAX_INTEGRAL_ERROR);
            --  Apply integral feedback
            Integ_FB_Gx := Rad_Gx + Integral_FBx;
            Integ_FB_Gy := Rad_Gy + Integral_FBy;
            Integ_FB_Gz := Rad_Gz + Integral_FBz;

         else
            Integral_FBx := 0.0;
            Integral_FBy := 0.0;
            Integral_FBz := 0.0;
         end if;

         --  Apply proportional feedback
         Rate_Change_Gx := Integ_FB_Gx + Two_Kp * Half_Ex;
         Rate_Change_Gy := Integ_FB_Gy + Two_Kp * Half_Ey;
         Rate_Change_Gz := Integ_FB_Gz + Two_Kp * Half_Ez;
      end if;

      --  Integrate rate of change of quaternion
      Rate_Change_Gx := Rate_Change_Gx * (0.5 * Dt);
      Rate_Change_Gy := Rate_Change_Gy * (0.5 * Dt);
      Rate_Change_Gz := Rate_Change_Gz * (0.5 * Dt);

      Q0_Tmp := Q0 +
        (-Qb * Rate_Change_Gx - Qc * Rate_Change_Gy - Q3 * Rate_Change_Gz);
      Q1_Tmp := Q1 +
        (Qa * Rate_Change_Gx + Qc * Rate_Change_Gz - Q3 * Rate_Change_Gy);
      Q2_Tmp := Q2 +
        (Qa * Rate_Change_Gy - Qb * Rate_Change_Gz + Q3 * Rate_Change_Gx);
      Q3_Tmp := Q3 +
        (Qa * Rate_Change_Gz + Qb * Rate_Change_Gy - Qc * Rate_Change_Gx);

      --  These asserts are only needed to help SPARK
      pragma Assert
        (Q0_Tmp in -4.0 * MAX_RATE_CHANGE .. 4.0 * MAX_RATE_CHANGE);
      pragma Assert
        (Q1_Tmp in -4.0 * MAX_RATE_CHANGE .. 4.0 * MAX_RATE_CHANGE);
      pragma Assert
        (Q2_Tmp in -4.0 * MAX_RATE_CHANGE .. 4.0 * MAX_RATE_CHANGE);
      pragma Assert
        (Q3_Tmp in -4.0 * MAX_RATE_CHANGE .. 4.0 * MAX_RATE_CHANGE);

      --  Normalize quaternions
      Recip_Norm := Inv_Sqrt (Q0_Tmp * Q0_Tmp + Q1_Tmp * Q1_Tmp +
                                Q2_Tmp * Q2_Tmp + Q3_Tmp * Q3_Tmp);
      Q0 := Saturate (Q0_Tmp * Recip_Norm,
                      T_Quaternion'First,
                      T_Quaternion'Last);
      Q1 := Saturate (Q1_Tmp * Recip_Norm,
                      T_Quaternion'First,
                      T_Quaternion'Last);
      Q2 := Saturate (Q2_Tmp * Recip_Norm,
                      T_Quaternion'First,
                      T_Quaternion'Last);
      Q3 := Saturate (Q3_Tmp * Recip_Norm,
                      T_Quaternion'First,
                      T_Quaternion'Last);
   end Mahony_Update_Q;


   procedure SensFusion6_Update_Q
     (Gx : T_Rate;
      Gy : T_Rate;
      Gz : T_Rate;
      Ax : T_Acc;
      Ay : T_Acc;
      Az : T_Acc;
      Dt : T_Delta_Time) is
   begin
      case SENSOR_FUSION_ALGORITHM is
         when MAHONY => Mahony_Update_Q (Gx,
                                         Gy,
                                         Gz,
                                         Ax,
                                         Ay,
                                         Az,
                                         Dt);
         when others => Madgwick_Update_Q (Gx,
                                           Gy,
                                           Gz,
                                           Ax,
                                           Ay,
                                           Az,
                                           Dt);
      end case;
   end SensFusion6_Update_Q;

   procedure SensFusion6_Get_Euler_RPY
     (Euler_Roll_Actual  : out T_Degrees;
      Euler_Pitch_Actual : out T_Degrees;
      Euler_Yaw_Actual   : out T_Degrees) is
      Grav_X : Float;
      Grav_Y : Float;
      Grav_Z : Float;
   begin
      --  Estimated gravity direction
      Grav_X := 2.0 * (Q1 * Q3 - Q0 * Q2);
      Grav_Y := 2.0 * (Q0 * Q1 + Q2 * Q3);
      Grav_Z := Q0 * Q0 - Q1 * Q1 - Q2 * Q2 + Q3 * Q3;

      Grav_X := Saturate (Grav_X, -1.0, 1.0);

      Euler_Yaw_Actual :=
        Atan (2.0 * (Q0 * Q3 + Q1 * Q2),
              Q0 * Q0 + Q1 * Q1 - Q2 * Q2 - Q3 * Q3) * 180.0 / Pi;
      --  Pitch seems to be inverted
      Euler_Pitch_Actual := Asin (Grav_X) * 180.0 / Pi;
      Euler_Roll_Actual := Atan (Grav_Y, Grav_Z) * 180.0 / Pi;
   end SensFusion6_Get_Euler_RPY;

   function SensFusion6_Get_AccZ_Without_Gravity
     (Ax : T_Acc;
      Ay : T_Acc;
      Az : T_Acc) return Float is
      Grav_X : Float range -4.0 .. 4.0;
      Grav_Y : Float range -4.0 .. 4.0;
      Grav_Z : Float range -4.0 .. 4.0;
   begin
      --  Estimated gravity direction

      Grav_X := 2.0 * (Q1 * Q3 - Q0 * Q2);

      Grav_Y := 2.0 * (Q0 * Q1 + Q2 * Q3);

      Grav_Z := Q0 * Q0 - Q1 * Q1 - Q2 * Q2 + Q3 * Q3;

      --  Feturn vertical acceleration without gravity
      --  (A dot G) / |G| - 1G (|G| = 1) -> (A dot G) - 1G
      return (Ax * Grav_X + Ay * Grav_Y + Az * Grav_Z) - 1.0;
   end SensFusion6_Get_AccZ_Without_Gravity;

end SensFusion6_Pack;
