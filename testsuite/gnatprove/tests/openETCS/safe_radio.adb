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

package body Safe_Radio is pragma SPARK_Mode (On);

   ----------------------
   -- Setup_Connection --
   ----------------------

   function Setup_Connection
     (phone : Data_Types.Telephone_Number_t)
      return Boolean
   is
      pragma SPARK_Mode (Off);
   begin
      --  Generated stub: replace with real body!
      raise Program_Error with "Unimplemented function Setup_Connection";
      return False;
   end Setup_Connection;

   procedure Send_Message(message : Message_Type_t) is
      pragma SPARK_Mode (Off);
   begin
      --  Generated stub: replace with real body!
      raise Program_Error with "Unimplemented function Setup_Connection";
   end Send_Message;
end Safe_Radio;
