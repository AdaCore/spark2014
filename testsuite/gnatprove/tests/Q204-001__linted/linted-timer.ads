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
with Ada.Real_Time;

package Linted.Timer is
   pragma Elaborate_Body;

   generic
      with procedure On_Tick;
   package Worker with
      Abstract_State => ((Reader with External), (Writer with External)) is
      procedure Wait_Until (Time : Ada.Real_Time.Time) with
         Global => (In_Out => Writer),
         Depends => (Writer => (Writer, Time));
   end Worker;
end Linted.Timer;
