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

-- Commented out because not supported in GNAT GPL 2012
--- with Ada.Containers.Formal_Hashed_Maps;
--- with Ada.Containers; use Ada.Containers;

with Data_Types; use Data_Types;

package Com_Map is pragma SPARK_Mode (On);
-- Commented out because not supported in GNAT GPL 2012
--     function RBC_RIU_ID_Hash(id : RBC_RIU_ID_t) return Hash_Type is
--       (Hash_Type(id));
--
--     package Com_To_RBC_Map is new Ada.Containers.Formal_Hashed_Maps
--       (Key_Type        => RBC_RIU_ID_t,
--        Element_Type    => Boolean, -- False: com being established
--                                    -- True : com established
--        Hash            => RBC_RIU_ID_Hash,
--        Equivalent_Keys => "=",
--        "="             => "=");
   type Com_Element is record
      Used            : Boolean := False; -- False: element not used
      Com_Established : Boolean := False; -- False: com being established
                                          -- True : com established
   end record;

   type Com_To_RBC_Map is array (RBC_RIU_ID_T) of Com_Element;

   function Contains (Map : Com_To_RBC_Map; Id : RBC_RIU_ID_T) return Boolean
   is (Map (Id).Used and Map(Id).Com_Established);
end;
