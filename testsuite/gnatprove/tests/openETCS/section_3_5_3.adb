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

with Appendix_A_3_1;
with Safe_Radio;
with ETCS_Level;

package body Section_3_5_3 is pragma SPARK_Mode (On);
   procedure Initiate_Communication_Session(destination : RBC_RIU_ID_t;
                                            phone : Telephone_Number_t) is
      connection_attemps : Natural := 0;
   begin
      -- SUBSET-026-3.5.3.7.a
      if Start_Of_Mission then
         while connection_attemps
           <= Appendix_A_3_1.number_of_times_try_establish_safe_radio_connection
         loop
            if Safe_Radio.Setup_Connection(phone) then
               return;
            end if;
            connection_attemps := connection_attemps + 1;
         end loop;
      else
         -- not part of on-going Start of Mission procedure
         loop
            -- FIXME How following asynchronous events are update within this
            -- loop? Should be we read state variable updated by external tasks?
            if Safe_Radio.Setup_Connection(phone)
              or End_Of_Mission
              or Track_Side_Terminate_Communication_Order
              or Train_Passes_Level_Transition_Border
              or (Order_To_Contact_Different_RBC -- FIXME badly formalized
                  and Contact_Order_Not_For_Accepting_RBC)
              or Train_Passes_RBC_RBC_Border
              or Train_Passes_Start_Of_Announced_Radio_Hole
              or (-- FIXME destination is an RIU
                  ETCS_Level.ertms_etcs_level /= 1)
            then
               return;
            end if;
         end loop;
      end if;

      -- SUBSET-026-3.5.3.7.b
      Safe_Radio.Send_Message(Safe_Radio.Initiation_Of_Communication);

      -- SUBSET-026-3.5.3.7.c not formalized (trackside)
   end;

   procedure Contact_RBC(RBC_identity : RBC_RIU_ID_t;
                         RBC_number : Telephone_Number_t;
                         Action : RBC_Contact_Action_t;
                         Apply_To_Sleeping_Units : Boolean) is
   begin
      null;
   end;

end;
