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
with System.Storage_Elements;

package Linted.Windows is
   pragma Pure;

   type Window is mod 2**32;

   Storage_Size : constant := 4;

   subtype Storage is
     System.Storage_Elements.Storage_Array (1 .. Storage_Size);

   procedure From_Storage (S : Storage; W : out Window);
end Linted.Windows;
