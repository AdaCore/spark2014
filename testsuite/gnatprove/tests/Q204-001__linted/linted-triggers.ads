-- Copyright 2017 Steven Stewart-Gallus
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
private with Linted.Wait_Lists;

package Linted.Triggers with
     Spark_Mode is
   pragma Preelaborate;

   type Waiter is private;
   type Signaller is private;

   Null_Waiter : constant Waiter;
   Null_Signaller : constant Signaller;

   generic
   package Handle with
      Spark_Mode is
      function Wait_Handle return Waiter with
         Pure_Function;
      function Signal_Handle return Signaller with
         Pure_Function;
   end Handle;

   function Is_Null_Waiter (W : Waiter) return Boolean;
   function Is_Null_Signaller (S : Signaller) return Boolean;

   procedure Wait (W : Waiter) with
      Global => null,
      Pre => not Is_Null_Waiter (W);
   procedure Signal (S : Signaller) with
      Global => null,
      Pre => not Is_Null_Signaller (S);
   procedure Broadcast (S : Signaller) with
      Global => null,
      Pre => not Is_Null_Signaller (S);

private
   pragma SPARK_Mode (Off);

   type Waiter is access all Wait_Lists.Wait_List;
   type Signaller is access all Wait_Lists.Wait_List;

   Null_Waiter : constant Waiter := null;
   Null_Signaller : constant Signaller := null;

end Linted.Triggers;
