-- Copyright 2015,2016,2017 Steven Stewart-Gallus
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
with Interfaces;

package body Linted.Windows is
   package Storage_Elements renames System.Storage_Elements;

   use type Interfaces.Unsigned_32;
   use type Storage_Elements.Storage_Offset;

   procedure From_Storage (S : Storage; W : out Window) is
   begin
      W :=
        Window
          (Interfaces.Unsigned_32 (S (1)) or
           Interfaces.Shift_Left (Interfaces.Unsigned_32 (S (2)), 8) or
           Interfaces.Shift_Left (Interfaces.Unsigned_32 (S (3)), 16) or
           Interfaces.Shift_Left (Interfaces.Unsigned_32 (S (4)), 24));
   end From_Storage;
end Linted.Windows;
