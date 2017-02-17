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

with ETCS_Level; use ETCS_Level;

with Data_Types; use Data_Types;

with Com_Map; use Com_Map;

package Section_3_5_3 is pragma SPARK_Mode (On);
   -- FIXME using SRS sections as package name is probably not the best approach

   -- SUBSET-026-3.5.3.4
   Start_Of_Mission : Boolean;
   End_of_Mission : Boolean;
   Track_Side_New_Communication_Order : Boolean;
   Track_Side_Terminate_Communication_Order : Boolean;
   Train_Passes_Level_Transition_Border : Boolean;
   Train_Passes_RBC_RBC_Border : Boolean;
   Train_Passes_Start_Of_Announced_Radio_Hole : Boolean;
   Order_To_Contact_Different_RBC : Boolean;
   Contact_Order_Not_For_Accepting_RBC : Boolean;
   Mode_Change_Report_To_RBC_Not_Considered_As_End_Of_Mission : Boolean; -- to be refined
   Manual_Level_Change : Boolean;
   Train_Front_Reaches_End_Of_Radio_Hole : Boolean;
   Previous_Communication_Loss : Boolean;
   Start_Of_Mission_Procedure_Completed_Without_Com : Boolean;

   Connections : Com_To_RBC_Map.Map(Capacity => 10,
                                    Modulus =>
                                      Com_To_RBC_Map.Default_Modulus(10));

   function Authorize_New_Communication_Session return Boolean is
     ((Start_Of_Mission = True
       and (ertms_etcs_level = 2 or ertms_etcs_level = 3)) -- SUBSET-026-3.5.3.4.a
      and Track_Side_New_Communication_Order = True -- SUBSET-026-3.5.3.4.b
      and (Mode_Change_Report_To_RBC_Not_Considered_As_End_Of_Mission = True
           and (ertms_etcs_level = 2 or ertms_etcs_level = 3))-- SUBSET-026-3.5.3.4.c
      and (Manual_Level_Change = True
           and (ertms_etcs_level = 2 or ertms_etcs_level = 3)) -- SUBSET-026-3.5.3.4.d
      and Train_Front_Reaches_End_Of_Radio_Hole = True -- SUBSET-026-3.5.3.4.e
      and Previous_Communication_Loss = True -- SUBSET-026-3.5.3.4.f
      and (Start_Of_Mission_Procedure_Completed_Without_Com = True
           and (ertms_etcs_level = 2 or ertms_etcs_level = 3)) -- SUBSET-026-3.5.3.4.g
     );

   -- SUBSET-026-3.5.3.1 and SUBSET-026-3.5.3.2 implicitly fulfilled as we model on-board
   procedure Initiate_Communication_Session(destination : RBC_RIU_ID_t;
                                            phone : Telephone_Number_t)
   with
     Pre => ((Authorize_New_Communication_Session = True) -- SUBSET-026-3.5.3.4
             and (not Contains(Connections,destination)) -- SUBSET-026-3.5.3.4.1
             -- FIXME: what should we do for cases f and g?
            ),
     Post => (Contains(Connections, destination));

   -- SUBSET-026-3.5.3.3 not formalized (Note)

   -- SUBSET-026-3.5.3.5
   procedure Contact_RBC(RBC_identity : RBC_RIU_ID_t;
                         RBC_number : Telephone_Number_t;
                         Action : RBC_Contact_Action_t;
                         Apply_To_Sleeping_Units : Boolean);

   -- SUBSET-026-3.5.3.5.1 to be formalized. The content of table SUBSET-026-3.5.3.16 should be
   -- incorporated as above operation post-condition (if possible)

   -- SUBSET-026-3.5.3.5.3 and SUBSET-026-3.5.3.6 not formalized (FIXME). Should be similar to
   -- SUBSET-026-3.5.3.5

   -- SUBSET-026-3.5.3.7 see body of Initiate_Communication_Session

   -- SUBSET-026-3.5.3.8 to SUBSET-026-3.5.3.16 not formalized (FIXME)
end;
