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
pragma Elaborate_All(Units);

package Deceleration_Curve is pragma SPARK_Mode (On);
   Distance_Resolution : constant Distance_t := 5; -- m

   Maximum_Valid_Speed : constant Speed_t :=
     m_per_s_From_km_per_h(Maximum_Valid_Speed_km_per_h);

   Minimum_Valid_Acceleration : constant Acceleration_t := -10.0; -- FIXME: realistic value?

   type Braking_Curve_Range is range 0..1_000;

   Braking_Curve_Maximum_End_Point : constant Distance_t :=
     Distance_t(Braking_Curve_Range'Last - Braking_Curve_Range'First)
     * Distance_Resolution;

   type Braking_Curve_Entry is
      record
         location : Distance_t;
         speed : Speed_t;
      end record;

   type Braking_Curve_Array is array (Braking_Curve_Range)
     of Braking_Curve_Entry;

   type Braking_Curve_t is
      record
         curve : Braking_Curve_Array;
         end_point : Distance_t;
      end record;

   -- SUBSET-026-3.13.8.1.1
   type Target_t is
      record
         supervise : Boolean;
         location : Distance_t;
         speed : Speed_t;
      end record;

   function Distance_To_Speed(Initial_Speed, Final_Speed: Speed_t;
                              Acceleration: Acceleration_t)
                              return Distance_t
   with
     Pre => (Initial_Speed > 0.0 and Final_Speed >= 0.0
             and
               Initial_Speed <= Maximum_Valid_Speed
             and
               Initial_Speed > Final_Speed
             and
               Acceleration < 0.0
             and
               Acceleration >= Minimum_Valid_Acceleration);

   function Curve_Index_From_Location(d : Distance_t)
                                      return Braking_Curve_Range
   with
   Pre => (d <= Braking_Curve_Maximum_End_Point);

   procedure Curve_From_Target(Target : Target_t;
                               Braking_Curve : out Braking_Curve_t)
   with
     Pre => (Target.location <= Braking_Curve_Maximum_End_Point);

   procedure Print_Curve(Braking_Curve : Braking_Curve_t);
end Deceleration_Curve;
