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
with Interfaces.C;
with System;

with Linted.Errors;
with Linted.KOs;

package Linted.Stdio with
     Spark_Mode => Off is
   pragma Elaborate_Body;

   procedure Write_Line (Object : Linted.KOs.KO; Str : String);

   procedure Write_String
     (Object : Linted.KOs.KO;
      Str : String;
      Err : out Linted.Errors.Error);

   procedure Write
     (Object : Linted.KOs.KO;
      Buf : System.Address;
      Count : Interfaces.C.size_t;
      Bytes_Written : out Interfaces.C.size_t;
      Err : out Linted.Errors.Error);
end Linted.Stdio;
