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

package Linted.Update is
   pragma Pure;

   type Int is range -2**(32 - 1) .. 2**(32 - 1) - 1;
   type Nat is mod 2**32;

   type Packet is record
      X_Position : Int := 0;
      Y_Position : Int := 0;
      Z_Position : Int := 0;

      MX_Position : Int := 0;
      MY_Position : Int := 0;
      MZ_Position : Int := 0;

      Z_Rotation : Nat := 0;
      X_Rotation : Nat := 0;
   end record;

   Storage_Size : constant := 8 * 4;

   subtype Storage is
     System.Storage_Elements.Storage_Array (1 .. Storage_Size);

   procedure To_Storage (U : Packet; S : out Storage);
   procedure From_Storage (S : Storage; U : out Packet);
end Linted.Update;
