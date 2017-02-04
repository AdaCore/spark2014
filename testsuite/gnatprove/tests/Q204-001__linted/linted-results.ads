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
with Linted.Errors;

generic
   type Element_T is private;
package Linted.Results with
   Abstract_State => null is
   pragma Preelaborate;

   type Result (Erroneous : Boolean) is record
      case Erroneous is
         when True =>
            Err : Errors.Error := 0;
         when False =>
            Data : Element_T;
      end case;
   end record;
end Linted.Results;
