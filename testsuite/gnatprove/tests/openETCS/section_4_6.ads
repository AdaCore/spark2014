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

with ETCS_Level;
use ETCS_Level;

with Section_4_3_2;
use Section_4_3_2;

package Section_4_6 is pragma SPARK_Mode (On);
   -- SUBSET-026-4.6.3 Transitions Conditions Table
   -- WARNING: not all conditions are modeled

   -- Individual condition elements
   an_acknowledge_request_for_shunting_is_displayed_to_the_driver : Boolean;

   driver_acknowledges : Boolean;

   driver_isolates_ERTMS_ETCS_on_board_equipment : Boolean;

   driver_selects_shunting_mode : Boolean;

   ma_ssp_gardient_on_board : Boolean;

   no_specific_mode_is_required_by_a_mode_profile : Boolean;

   note_5_conditions_for_shunting_mode : Boolean;

   reception_of_information_shunting_granted_by_rbc : Boolean;

   train_is_at_standstill : Boolean;

   valid_train_data_is_stored_on_board : Boolean;

   -- Conditions
   function condition_1 return Boolean is
     (driver_isolates_ERTMS_ETCS_on_board_equipment);

   function condition_5 return Boolean is
     (train_is_at_standstill
      AND (ertms_etcs_level = 0 OR ertms_etcs_level = ertms_etcs_level_ntc
           OR ertms_etcs_level = 1)
      AND driver_selects_shunting_mode);

   function condition_6 return Boolean is
     (train_is_at_standstill
      AND (ertms_etcs_level = 2 OR ertms_etcs_level = 3)
      AND reception_of_information_shunting_granted_by_rbc);

   function condition_10 return Boolean is
     (valid_train_data_is_stored_on_board
      AND ma_ssp_gardient_on_board
      AND no_specific_mode_is_required_by_a_mode_profile);

   function condition_50 return Boolean is
     (an_acknowledge_request_for_shunting_is_displayed_to_the_driver
      AND driver_acknowledges
      AND note_5_conditions_for_shunting_mode);

   -- SUBSET-026-4.6.2 Transitions Table
   type priority_t is range 1..7;
   priority : priority_t;

   function condition_transition_SB_to_SH return Boolean is
     ((condition_5 OR condition_6 OR condition_50) AND priority = 7);

   function condition_transition_SB_to_FS return Boolean is
     (condition_10 AND priority = 7);

   function condition_transition_SB_to_IS return Boolean is
     (condition_1 AND priority = 1);

   -- following function is no longer needed
   function disjoint_condition_transitions return Boolean is
     (NOT(condition_transition_SB_to_SH = True
          AND condition_transition_SB_to_FS = True)
      AND NOT(condition_transition_SB_to_SH = True
              AND condition_transition_SB_to_IS = True)
      AND NOT(condition_transition_SB_to_FS = True
              AND condition_transition_SB_to_IS = True));

   function transition(mode : etcs_mode_t) return etcs_mode_t
   with
--       Post => (disjoint_condition_transitions = True);
     -- SUBSET-026-4.6.1.5: all cases are disjoint
     Contract_Cases => (condition_transition_SB_to_SH => True,
                        condition_transition_SB_to_FS => True,
                        condition_transition_SB_to_IS => True),
     Post => True; -- work around for bug in SPARK Hi-Lite GPL 2013
end;
