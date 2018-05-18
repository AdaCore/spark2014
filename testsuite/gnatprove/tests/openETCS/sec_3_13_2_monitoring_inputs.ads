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

with Units; use Units;
pragma Elaborate_All(Units);
with Step_Function; use Step_Function;

package sec_3_13_2_monitoring_inputs is pragma SPARK_Mode (On);
   -- *** section 3.13.2.2 Train related inputs ***
   -- ** section 3.13.2.2.1 Introduction **

   -- SUBSET-026-3.13.2.2.1.1 not formalized (description)

   -- SUBSET-026-3.13.2.2.1.2 not formalized

   -- SUBSET-026-3.13.2.2.1.3
   type Breaking_Model_t is (Train_Data_Model, Conversion_Model);
   -- Only Train Data model is modelized
   Breaking_Model : constant Breaking_Model_t := Train_Data_Model;


   -- ** section 3.13.2.2.2 Traction model **

   -- SUBSET-026-3.13.2.2.2.1
   T_traction_cut_off : constant Time_t := 10.0; -- s -- FIXME: realistic value?

   -- SUBSET-026-3.13.2.2.2.2 not formalized (Note)


   -- ** section 3.13.2.2.3 Braking Models **

   -- SUBSET-026-3.13.2.2.3.1.1
   -- Use Step_Function.Step_Function_t type

   -- SUBSET-026-3.13.2.2.3.1.2
   -- Note: It would be better to modelize this as Data type invariant
   function Is_Valid_Deceleration_Model(S : Step_Function_t) return Boolean is
     (Step_Function.Is_Valid(S)
      and
        (S.Number_Of_Delimiters <= 6)); -- 6 delimiters for 7 steps

   -- SUBSET-026-3.13.2.2.3.1.3 not formalized (Note)

   -- SUBSET-026-3.13.2.2.3.1.4
   -- by definition of Step_Function.Step_Function_t

   -- SUBSET-026-3.13.2.2.3.1.5 not formalized (FIXME?)

   -- SUBSET-026-3.13.2.2.3.1.6
   A_brake_emergency_model : constant Step_Function_t :=
     (Number_Of_Delimiters => 0,
      Step => ((0, 1.0), -- (from 0 m/s, 1 m/s**2)
               others => (0, 0.0)));

   A_brake_service_model : Step_Function_t; -- FIXME give value, set constant

   A_brake_normal_service_model : Step_Function_t; -- FIXME give value, set constant

   -- SUBSET-026-3.13.2.2.3.1.7 not formalized (we do not consider regenerative
   -- brake, eddy current brake and magnetic shoe brake)

   -- SUBSET-026-3.13.2.2.3.1.8 not formalized (Note)

   -- SUBSET-026-3.13.2.2.3.1.9
   type Brake_Position_t is (Freight_Train_In_G, Passenger_Train_In_P,
                             Freight_Train_In_P);


   A_SB01 : constant Deceleration_t := 0.1;
   A_SB02 : constant Deceleration_t := 0.2;

   -- SUBSET-026-3.13.2.2.3.1.10 not formalized FIXME
--     function A_Brake_normal_service(V : Speed_t; position : Brake_Position_t)
--                                     return Deceleration_t;

   -- SUBSET-026-3.13.2.2.3.1.11 not formalized (Note)

   -- SUBSET-026-3.13.2.2.3.2.1 not formalized (description)
   -- SUBSET-026-3.13.2.2.3.2.2 not formalized (figure)

   -- SUBSET-026-3.13.2.2.3.2.3
   T_brake_react : constant Time_t := 1.0; -- s
   T_brake_increase : constant Time_t := 2.0; -- s

   -- SUBSET-026-3.13.2.2.3.2.4
   T_brake_build_up : constant Time_t := T_brake_react + 0.5 * T_brake_increase;

   -- SUBSET-026-3.13.2.2.3.2.5
   T_brake_emergency_react : constant Time_t := T_brake_react;
   T_brake_emergency_increase : constant Time_t := T_brake_increase;
   T_brake_emergency : constant Time_t :=
     T_brake_emergency_react + 0.5 * T_brake_emergency_increase;

   T_brake_service_react : constant Time_t := T_brake_react;
   T_brake_service_increase : constant Time_t := T_brake_increase;
   T_brake_service : constant Time_t :=
     T_brake_service_react + 0.5 * T_brake_service_increase;

   -- SUBSET-026-3.13.2.2.3.2.6 not formalized (Note)

   -- SUBSET-026-3.13.2.2.3.2.7 not formalized (Note)

   -- SUBSET-026-3.13.2.2.3.2.8 not formalized (we do not consider regenerative
   -- brake, eddy current brake and magnetic shoe brake)

   -- SUBSET-026-3.13.2.2.3.2.9 not formalized (Note)

   -- SUBSET-026-3.13.2.2.3.2.10 not formalized (Note)

   -- ** section 3.13.2.2.4 Brake Position **

   -- SUBSET-026-3.13.2.2.4.1
   -- see type Brake_Position_t definition above

   -- SUBSET-026-3.13.2.2.4.2 not formalized (Note)


   -- ** section 3.13.2.2.5 Brake Percentage ** not formalized (conversion model
   -- not used)

   -- ** section 3.13.2.2.6 Special Brakes ** not formalized (special brake not
   -- modelized)


   -- ** section 3.13.2.2.7 Service brake interface **

   -- SUBSET-026-3.13.2.2.7.1
   Service_Brake_Command_Implemented : constant Boolean := True;

   -- SUBSET-026-3.13.2.2.7.2
   Service_Brake_Feedback_Implemented : constant Boolean := True;

   -- ** section 3.13.2.2.8 Traction cut-off interface **

   -- SUBSET-026-3.13.2.2.8.1
   Traction_Cut_Off_Command_Implemented : constant Boolean := True;


   -- ** section 3.13.2.2.9 On-borad Correction Factors **

   -- SUBSET-026-3.13.2.2.9.1.1 not formalized (description)

   -- SUBSET-026-3.13.2.2.9.1.2
   Kdry_rst_model : constant Step_Function_t :=
     (Number_Of_Delimiters => 0,
      Step => ((0, 1.0), -- (from 0 m/s, 1.0)
               others => (0, 0.0)));

   Kwet_rst_model : constant Step_Function_t :=
     (Number_Of_Delimiters => 0,
      Step => ((0, 1.0), -- (from 0 m/s, 1.0)
               others => (0, 0.0)));

   -- SUBSET-026-3.13.2.2.9.1.3
   -- FIXME EBCL parameter not formalized
   function Is_Valid_Kdry_rst return Boolean is
     (Step_Function.Is_Valid(Kdry_rst_model)
      and
        (Has_Same_Delimiters(Kdry_rst_model, A_brake_emergency_model)));

   function Kdry_rst(V: Speed_t) return Float
   with
     Pre => Is_Valid_Kdry_rst,
     Post =>
       (Kdry_rst'Result
        = Step_Function.Get_Value(SFun => Kdry_rst_model,
                                  X    => Function_Range(V)));

   -- SUBSET-026-3.13.2.2.9.1.4 not formalized (FIXME)

   -- SUBSET-026-3.13.2.2.9.1.5
   function Is_Valid_Kwet_rst return Boolean is
     (Step_Function.Is_Valid(Kwet_rst_model)
      and
        (Has_Same_Delimiters(Kwet_rst_model, A_brake_emergency_model)));

   function Kwet_rst(V: Speed_t) return Float
   with
     Pre => Is_Valid_Kwet_rst,
     Post =>
       (Kwet_rst'Result
        = Step_Function.Get_Value(SFun => Kwet_rst_model,
                                  X    => Function_Range(V)));

   -- SUBSET-026-3.13.2.2.9.2.1
   type Gradient_Range is new Float range 0.0 .. 10.0; -- m/s**2

   Kn_Plus : Step_Function_t;
   Kn_Minus : Step_Function_t;

   -- SUBSET-026-3.13.2.2.9.2.2
   -- Note: It would be better to modelize this as Data type invariant
   function Is_Valid_Kn return Boolean is
     (Step_Function.Is_Valid(Kn_Plus) and Step_Function.Is_Valid(Kn_Minus)
      and
        (Kn_Plus.Number_Of_Delimiters <= 4) -- 4 delimiters for 5 steps
      and
        (Kn_Minus.Number_Of_Delimiters <= 4)); -- 4 delimiters for 5 steps

   -- SUBSET-026-3.13.2.2.9.2.3 not formalized (Note)

   -- SUBSET-026-3.13.2.2.9.2.4 not formalized (FIXME)

   -- SUBSET-026-3.13.2.2.9.2.5 not formalized (FIXME)

   -- SUBSET-026-3.13.2.2.9.2.6
   -- By definition of Step_Function_t

   -- ** section 3.13.2.2.10 Nominal Rotating mass **

   -- SUBSET-026-3.13.2.2.10.1 not formalized (FIXME)

   -- ** section 3.13.2.2.11 Train length **

   -- SUBSET-026-3.13.2.2.11.1
   Train_Length : constant Distance_t := 900; -- m

   -- ** section 3.13.2.2.12 Fixed Values **

   -- SUBSET-026-3.13.2.2.12.1 not formalized (description)

   -- ** section 3.13.2.2.13 Maximum train speed **

   -- SUBSET-026-3.13.2.2.12.1
   Maximum_Train_Speed : constant Speed_t := m_per_s_From_km_per_h(250.0);

   -- *** section 3.13.2.3 Trackside related inputs ***
   -- all sections of 3.13.2.3 not formalized
   procedure dummy;
end sec_3_13_2_monitoring_inputs;
