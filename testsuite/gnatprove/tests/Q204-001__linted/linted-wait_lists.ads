-- Copyright 2016,2017 Steven Stewart-Gallus
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
package Linted.Wait_Lists with
     Spark_Mode is
   pragma Preelaborate;

   type Node_Nonnull_Access is private;
   type Node_Access is private;

   protected type Wait_List is
      procedure Insert (N : Node_Nonnull_Access) with
         Global => null,
         Depends => (Wait_List => (N, Wait_List));
      procedure Remove (N : Node_Nonnull_Access) with
         Global => null,
         Depends => (Wait_List => (N, Wait_List));
      procedure Broadcast with
         Global => null,
         Depends => (Wait_List => Wait_List);
      procedure Signal with
         Global => null,
         Depends => (Wait_List => Wait_List);

   private
      First : Node_Access;
      Last : Node_Access;
      Pending_Signal : Boolean := False;
   end Wait_List;

   procedure Wait (W : in out Wait_List) with
      Global => null,
      Depends => (W => W);
   procedure Broadcast (W : in out Wait_List) with
      Global => null,
      Depends => (W => W);
   procedure Signal (W : in out Wait_List) with
      Global => null,
      Depends => (W => W);

private
   pragma SPARK_Mode (Off);

   type Node;
   type Node_Nonnull_Access is not null access all Node;
   type Node_Access is access all Node;
end Linted.Wait_Lists;
