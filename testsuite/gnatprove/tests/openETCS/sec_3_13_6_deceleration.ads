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

with Step_Function; use Step_Function;
with Appendix_A_3_1; use Appendix_A_3_1;
with sec_3_13_2_monitoring_inputs; use sec_3_13_2_monitoring_inputs;
with sec_3_13_4_gradient_accel_decel; use sec_3_13_4_gradient_accel_decel;

package sec_3_13_6_deceleration is pragma SPARK_Mode (On);
   -- SUBSET-026-3.13.6.2.1 to 3.13.6.2.1.2 not formalized (FIXME)

   -- SUBSET-026-3.13.6.2.1.5 (Note .5 before .4 for proper definition)
   -- Note: we are not using specific break configuration so parameter 'd' is
   -- never used
   function A_brake_emergency(V: Speed_t; d: Distance_t) return Deceleration_t
   with
     Pre => (Is_Valid_Deceleration_Model(A_brake_emergency_model)
             and Is_Valid_Speed(V)),
   Post =>
     (A_brake_emergency'Result
      = Deceleration_t(Step_Function.Get_Value(SFun => A_brake_emergency_model,
                                               X    => Function_Range(V))));

   -- SUBSET-026-3.13.6.2.1.4 (Note .4 before .3 for proper definition)
   function A_brake_safe(V: Speed_t; d: Distance_t) return Deceleration_t is
     (Deceleration_t((Kdry_rst(V)
                      * (KWet_rst(V) + M_NVAVADH * (1.0 - Kwet_rst(V))))
                     * Float(A_brake_emergency(V,d))));

   -- SUBSET-026-3.13.6.2.1.3
   -- FIXME reduced adhesion condition not formalized
   function A_safe(V: Speed_t; d: Distance_t) return Deceleration_t is
     (A_brake_safe(V, d) + A_gradient(d));

   -- SUBSET-026-3.13.6.2.1.6 not formalized (conversion model not used)

   -- SUBSET-026-3.13.6.2.1.7 not formalized (same requirements as
   -- SUBSET-026-3.13.2.2.9.1.3)

   -- SUBSET-026-3.13.6.2.1.8 not formalized (conversion model not used)
   -- SUBSET-026-3.13.6.2.1.8.1 not formalized (conversion model not used)
   -- SUBSET-026-3.13.6.2.1.8.2 not formalized (conversion model not used)

   -- SUBSET-026-3.13.6.2.1.9 not formalized (Note)

   -- SUBSET-026-3.13.6.2.2.1 not formalized (description)

   -- SUBSET-026-3.13.6.2.2.2.a not formalized (FIXME?)
   -- SUBSET-026-3.13.6.2.2.2.b not formalized (conversion model not used)
   -- SUBSET-026-3.13.6.2.2.2.c not formalized (various brakes not modelled)

   -- SUBSET-026-3.13.6.2.2.3
   T_be : constant Time_t := T_brake_emergency;
end sec_3_13_6_deceleration;
