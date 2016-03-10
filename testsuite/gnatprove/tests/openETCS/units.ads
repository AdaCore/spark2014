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

package Units is pragma SPARK_Mode (On);
   -- For Breaking Curves computation
   subtype Speed_t is Float; -- m/s unit
   type Speed_km_per_h_t is new Float; -- km/h unit
   type Acceleration_t is new Float; -- m/s**2 unit
   type Deceleration_t is new Float range 0.0..Float'Last; -- m/s**2 unit
   type Distance_t is new Natural; -- m unit
   type Time_t is new Float; -- s unit

   Maximum_Valid_Speed_km_per_h : constant Speed_km_per_h_t := 500.0;-- 500 km/h

   function Is_Valid_Speed_km_per_h(Speed: Speed_km_per_h_t) return Boolean is
     (Speed >= 0.0 and Speed <= Maximum_Valid_Speed_km_per_h);

   function m_per_s_From_km_per_h(Speed: Speed_km_per_h_t) return Speed_t
   is
     (Speed_t((Speed * 1000.0) / 3600.0))
   with
     Pre => Is_Valid_Speed_km_per_h(Speed);

   function Is_Valid_Speed(Speed : Speed_t) return Boolean is
     (Speed >= 0.0
      and Speed <= m_per_s_From_km_per_h(Maximum_Valid_Speed_km_per_h));

   function km_per_h_From_m_per_s(Speed: Speed_t) return Speed_km_per_h_t
   with
     Pre => Is_Valid_Speed(Speed);

end Units;
