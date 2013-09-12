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

package body sec_3_13_6_deceleration is pragma SPARK_Mode (On);
   function A_brake_emergency(V: Speed_t; d: Distance_t) return Deceleration_t
   is
   begin
      return
        Deceleration_t(Step_Function.Get_Value(SFun => A_brake_emergency_model,
                                               X    => Function_Range(V)));
   end;
end sec_3_13_6_deceleration;
