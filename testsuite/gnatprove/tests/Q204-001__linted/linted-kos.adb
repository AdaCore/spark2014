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
with Interfaces.C.Strings;

package body Linted.KOs is
   package C renames Interfaces.C;

   function Open
     (Pathname : String;
      Flags : Open_Flags) return KO_Results.Result with
      Spark_Mode => Off is

      use type Linted.Errors.Error;
      use type C.unsigned;

      X : aliased C.char_array := C.To_C (Pathname);
      Err : Errors.Error;
      Fd : C.int;

      Has_Read_Only : constant Boolean := (Flags and Read_Only) /= 0;
      Has_Write_Only : constant Boolean := (Flags and Write_Only) /= 0;
      Has_Read_Write : constant Boolean := (Flags and Read_Write) /= 0;
   begin
      return (Erroneous => True, Err => Errors.Success);
   end Open;

   function Close (Object : KOs.KO) return Errors.Error with
      Spark_Mode => Off is
   begin
      return Errors.Success;
   end Close;

   function Pread
     (Object : KO;
      Buf : System.Address;
      Count : Interfaces.C.size_t;
      Offset :Interfaces.C.size_t;
      Bytes_Read : out Interfaces.C.size_t) return Errors.Error with
      Spark_Mode => Off is
   begin
      return Errors.Success;
   end Pread;
end Linted.KOs;
