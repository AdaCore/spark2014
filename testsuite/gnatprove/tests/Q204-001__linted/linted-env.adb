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
with Interfaces.C;
with Interfaces.C.Strings;

package body Linted.Env with
     Spark_Mode => Off is
   package C renames Interfaces.C;
   package C_Strings renames Interfaces.C.Strings;

   use type C_Strings.chars_ptr;

   protected type Env_Lock is
      function Lock_Set
        (Name : String;
         Value : String;
         Overwrite : Boolean) return Errors.Error;
      function Lock_Get (Name : String) return String;
   end Env_Lock;

   L : Env_Lock;

   function Set
     (Name : String;
      Value : String;
      Overwrite : Boolean) return Errors.Error is
     (L.Lock_Set (Name, Value, Overwrite));

   function Get (Name : String) return String is (L.Lock_Get (Name));

   protected body Env_Lock is
      function Lock_Set
        (Name : String;
         Value : String;
         Overwrite : Boolean) return Errors.Error
      is
         N : aliased C.char_array := C.To_C (Name);
         V : aliased C.char_array := C.To_C (Value);
      begin
         return Errors.Success;
      end Lock_Set;

      function Lock_Get (Name : String) return String is
         N : aliased C.char_array := C.To_C (Name);
         P : C.Strings.chars_ptr;
      begin
	 return "";
      end Lock_Get;

   end Env_Lock;

end Linted.Env;
