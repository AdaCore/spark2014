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

-- Reference: UNISIG SUBSET-026-3 v3.3.0

package body sec_3_13_2_monitoring_inputs is pragma SPARK_Mode (On);
--     function A_Brake_normal_service(V : Speed_t; position : Brake_Position_t)
--                                     return Deceleration_t is
--     begin
--        return 0.0;
--     end;
   function Kdry_rst(V: Speed_t) return Float is
   begin
      return Step_Function.Get_Value(SFun => Kdry_rst_model,
                                     X    => Function_Range(V));
   end;

   function Kwet_rst(V: Speed_t) return Float is
   begin
      return Step_Function.Get_Value(SFun => Kwet_rst_model,
                                     X    => Function_Range(V));
   end;

   procedure dummy is
   begin
      null;
   end;

end sec_3_13_2_monitoring_inputs;
