--  copyright 2013 David MENTRE <d.mentre@fr.merce.mee.com>
--                                 -- Mitsubishi Electric R&D Centre Europe
--
--  Licensed under the EUPL V.1.1 or - as soon they will be approved by
--  the European Commission - subsequent versions of the EUPL (the
--  "Licence");
--  You may not use this work except in compliance with the Licence.
--
--  You may obtain a copy of the Licence at:
--
--    http://joinup.ec.europa.eu/software/page/eupl/licence-eupl
--
--  Unless required by applicable law or agreed to in writing, software
--  distributed under the Licence is distributed on an "AS IS" basis,
--  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
--  implied.
--
--  See the Licence for the specific language governing permissions and
--  limitations under the Licence.

with Units; use Units;
with Ada.Numerics.Elementary_Functions;
with GNAT.IO; use GNAT.IO;
with sec_3_13_6_deceleration; use sec_3_13_6_deceleration;

package body Deceleration_Curve is pragma SPARK_Mode (On);
   Minimum_Valid_Speed : constant Speed_t := 0.1; -- m/s

   function Distance_To_Speed(Initial_Speed, Final_Speed: Speed_t;
                              Acceleration: Acceleration_t)
                              return Distance_t is
      speed : Speed_t := Initial_Speed;
      delta_speed : Speed_t;
      distance : Distance_t := 0;
   begin
      while speed > final_speed and speed > Minimum_Valid_Speed loop
         Pragma Assert (Minimum_Valid_Acceleration <= Acceleration
                        and Acceleration < 0.0);
         Pragma Loop_Invariant
           (Minimum_Valid_Speed < speed and speed <= Initial_Speed);
         Pragma Assert (0.0 < 1.0/speed and 1.0/speed < 1.0 / Minimum_Valid_Speed);
         Pragma assert
           ((Speed_t(Minimum_Valid_Acceleration) / Minimum_Valid_Speed)
            <= Speed_t(Acceleration) / speed);
         Pragma assert
           ((Speed_t(Minimum_Valid_Acceleration) / Minimum_Valid_Speed)
            * Speed_t(Distance_Resolution)
            <= (Speed_t(Acceleration) / speed) * Speed_t(Distance_Resolution));

         delta_speed := (Speed_t(Acceleration) / speed)
           * Speed_t(Distance_Resolution);

         Pragma Assert
           ((Speed_t(Minimum_Valid_Acceleration) / Minimum_Valid_Speed)
            * Speed_t(Distance_Resolution) <= delta_speed
            and
              delta_speed < 0.0);

         speed := speed + delta_speed;

         distance := distance + Distance_Resolution;
      end loop;

      return distance;
   end;

   function Curve_Index_From_Location(d : Distance_t)
                                      return Braking_Curve_Range is
   begin
      return Braking_Curve_Range(d / Distance_Resolution);
   end;

   procedure Curve_From_Target(Target : Target_t;
                               Braking_Curve : out Braking_Curve_t) is
      use Ada.Numerics.Elementary_Functions;

      speed : Speed_t := Target.speed;
      location : Distance_t := Target.location;
      end_point : constant Braking_Curve_Range :=
        Curve_Index_From_Location(Target.location);
   begin
      Braking_Curve.end_point := Target.location;
      Braking_Curve.curve(end_point).location := location;
      Braking_Curve.curve(end_point).speed := speed;

      for i in reverse Braking_Curve_Range'First .. end_point - 1 loop
         speed :=
           (speed + Sqrt(speed * speed
            + (Speed_t(4.0) * Speed_t(A_safe(speed, location)))
            * Speed_t(Distance_Resolution))) / 2.0;
         if speed > Maximum_Valid_Speed then
            speed := Maximum_Valid_Speed;
         end if;

         location := Distance_t(i) * Distance_Resolution;

         Braking_Curve.curve(i).location := location;
         Braking_Curve.curve(i).speed := speed;
      end loop;
   end Curve_From_Target;

   procedure Print_Curve(Braking_Curve : Braking_Curve_t) is
   begin
      for i in Braking_Curve_Range'First ..
        Curve_Index_From_Location(Braking_Curve.end_point) loop
         Put(Distance_t'Image(Braking_Curve.curve(i).location));
         Put(",   ");
         Put(Speed_km_per_h_t'Image(
           km_per_h_From_m_per_s(Braking_Curve.curve(i).speed)));
         New_Line;

         if Braking_Curve.curve(i).location >= Braking_Curve.end_point then
            exit;
         end if;
      end loop;
   end Print_Curve;
end Deceleration_Curve;
