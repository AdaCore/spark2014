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

package Section_4_3_2 is pragma SPARK_Mode (On);
   type etcs_mode_t is (Full_Supervision,
                        Limited_SUpervision,
                        On_Sight,
                        Staff_Responsible,
                        Shunting,
                        Unfitted,
                        Passive_Shunting,
                        Sleeping,
                        Stand_By,
                        Trip,
                        Post_Trip,
                        System_Failure,
                        Isolation,
                        No_Power,
                        Non_Leading,
                        National_System,
                        Reversing);

   type etcs_short_mode_t is (FS,
                              LS,
                              OS,
                              SR,
                              SH,
                              UN,
                              PS,
                              SL,
                              SB,
                              TR,
                              PT,
                              SF,
                              ISo, -- "IS" is a reserved Ada keyword
                              NP,
                              NL,
                              SN,
                              RV);
end;
