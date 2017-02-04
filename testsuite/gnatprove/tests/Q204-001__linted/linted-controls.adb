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
with Interfaces;

package body Linted.Controls is
   package Storage_Elements renames System.Storage_Elements;

   use type Interfaces.Unsigned_8;
   use type Interfaces.Unsigned_32;
   use type Storage_Elements.Storage_Offset;

   type Nat is mod 2**32;

   subtype Tuple is Storage_Elements.Storage_Array (1 .. 4);

   function To_Int (T : Tuple) return Int;
   function From_Bytes (T : Tuple) return Nat;

   function From_Bytes (T : Tuple) return Nat is
   begin
      return Nat
          (Interfaces.Unsigned_32 (T (4)) or
           Interfaces.Shift_Left (Interfaces.Unsigned_32 (T (3)), 8) or
           Interfaces.Shift_Left (Interfaces.Unsigned_32 (T (2)), 16) or
           Interfaces.Shift_Left (Interfaces.Unsigned_32 (T (1)), 24));
   end From_Bytes;

   function To_Int (T : Tuple) return Int is
      X : Nat;
      Y : Int;
   begin
      X := From_Bytes (T);
      if X <= Nat (Int'Last) then
         Y := Int (X);
      else
         Y := -Int (not X) - 1;
      end if;
      return Y;
   end To_Int;

   procedure From_Storage (S : Storage; C : out Packet) is
   begin
      C.Z_Tilt := To_Int (S (1 .. 4));
      C.X_Tilt := To_Int (S (5 .. 8));

      C.Left :=
        (Interfaces.Unsigned_8 (S (9)) and Interfaces.Shift_Left (1, 8 - 1)) /=
        0;
      C.Right :=
        (Interfaces.Unsigned_8 (S (9)) and Interfaces.Shift_Left (1, 8 - 2)) /=
        0;
      C.Forward :=
        (Interfaces.Unsigned_8 (S (9)) and Interfaces.Shift_Left (1, 8 - 3)) /=
        0;
      C.Back :=
        (Interfaces.Unsigned_8 (S (9)) and Interfaces.Shift_Left (1, 8 - 4)) /=
        0;

      C.Jumping :=
        (Interfaces.Unsigned_8 (S (9)) and Interfaces.Shift_Left (1, 8 - 5)) /=
        0;
   end From_Storage;

end Linted.Controls;
