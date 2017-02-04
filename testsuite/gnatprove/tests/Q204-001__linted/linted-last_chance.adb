-- Copyright 2015,2016 Steven Stewart-Gallus
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
-- implied.  See the License for the specific language governing
-- permissions and limitations under the License.
private with Ada.Exceptions;
private with Ada.Unchecked_Conversion;
with System;
private with Interfaces.C;
private with Interfaces.C.Strings;

package body Linted.Last_Chance with
     Spark_Mode => Off is
   package Exceptions renames Ada.Exceptions;

   procedure Last_Chance_Handler (Except : Exceptions.Exception_Occurrence);
   pragma Export (C, Last_Chance_Handler, "__gnat_last_chance_handler");

   procedure Last_Chance_Handler (Except : Exceptions.Exception_Occurrence) is
      function Convert is new Ada.Unchecked_Conversion
        (Interfaces.C.Strings.chars_ptr,
         System.Address);

      X : aliased Interfaces.C.char_array :=
        Interfaces.C.To_C (Exceptions.Exception_Information (Except));
      P : Interfaces.C.Strings.chars_ptr :=
        Interfaces.C.Strings.To_Chars_Ptr (X'Unchecked_Access);
      Res : Interfaces.C.long;
   begin
      loop
         null;
      end loop;
   end Last_Chance_Handler;
end Linted.Last_Chance;
