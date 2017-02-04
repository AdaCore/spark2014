-- Copyright 2016 Steven Stewart-Gallus
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
with Ada.Command_Line;

with Interfaces.C;
with Interfaces.C.Strings;

package body Linted.Logs is
   package C renames Interfaces.C;
   package C_Strings renames Interfaces.C.Strings;

   use type C.unsigned;

   procedure Log (Pri : Priority; Str : String) with
      Spark_Mode => Off is
      Sys_Pri : C.int;
   begin
      null;
   end Log;

end Linted.Logs;
