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

package body Linted.Triggers with
     Spark_Mode => Off is
   package body Handle with
        Spark_Mode => Off is
      Wait_List : aliased Wait_Lists.Wait_List;

      function Wait_Handle return Waiter is (Wait_List'Access);
      function Signal_Handle return Signaller is (Wait_List'Access);
   end Handle;

   function Is_Null_Waiter (W : Waiter) return Boolean is (W = null);
   function Is_Null_Signaller (S : Signaller) return Boolean is (S = null);

   procedure Wait (W : Waiter) is
   begin
      Wait_Lists.Wait (W.all);
   end Wait;

   procedure Signal (S : Signaller) is
   begin
      Wait_Lists.Signal (S.all);
   end Signal;

   procedure Broadcast (S : Signaller) is
   begin
      Wait_Lists.Broadcast (S.all);
   end Broadcast;
end Linted.Triggers;
