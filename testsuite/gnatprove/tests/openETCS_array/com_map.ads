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

with Data_Types; use Data_Types;

package Com_Map is
   type Com_Element is record
      Used  : Boolean := False; -- False: element not used
      Value : Boolean := False; -- False: com being established
                                -- True : com established
   end record;

   type Com_To_RBC_Map is array (RBC_RIU_ID_T) of Com_Element;

   function Contains (Map : Com_To_RBC_Map; Id : RBC_RIU_ID_T) return Boolean
   is (Map (Id).Used and Map(Id).Value);
end;
