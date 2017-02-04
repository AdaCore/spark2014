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
with Ada.Synchronous_Task_Control;

package body Linted.Wait_Lists with
     Spark_Mode => Off is
   package STC renames Ada.Synchronous_Task_Control;

   type Node is record
      Trigger : STC.Suspension_Object;
      Prev_Trigger : Node_Access;
      Next_Trigger : Node_Access;
   end record;

   protected body Wait_List is
      procedure Insert (N : Node_Nonnull_Access) is
      begin
	 pragma Assert (N.Next_Trigger = null);
	 pragma Assert (N.Prev_Trigger = null);

	 if Pending_Signal then
	    STC.Set_True (N.Trigger);
	    Pending_Signal := False;
	 end if;

         if First = null or Last = null then
            First := Node_Access (N);
         else
	    N.Prev_Trigger := Last;
            Last.Next_Trigger := Node_Access (N);
         end if;
         Last := Node_Access (N);
      end Insert;

      procedure Remove (N : Node_Nonnull_Access) is
	 Prev : Node_Access;
	 Next : Node_Access;
      begin
	 Prev := N.Prev_Trigger;
	 Next := N.Next_Trigger;

	 if null = Prev then
	    First := Next;
	 else
	    Prev.Next_Trigger := Next;
	 end if;

	 if null = Next then
	    Last := Prev;
	 else
	    Next.Prev_Trigger := Prev;
	 end if;
      end Remove;

      procedure Broadcast is
         Current_Trigger : Node_Access;
      begin
         Current_Trigger := First;
	 if null = Current_Trigger then
	    Pending_Signal := True;
	 else
	    loop
	       STC.Set_True (Current_Trigger.Trigger);
	       Current_Trigger := Current_Trigger.Next_Trigger;
	       exit when null = Current_Trigger;
	    end loop;
	 end if;
      end Broadcast;

      procedure Signal is
         Current_Trigger : Node_Access;
      begin
         Current_Trigger := First;

         if null = Current_Trigger then
	    Pending_Signal := True;
	 else
            STC.Set_True (Current_Trigger.Trigger);
         end if;
      end Signal;
   end Wait_List;

   procedure Wait (W : in out Wait_List) is
      N : aliased Node;
      use type Wait_List;
   begin
      W.Insert (N'Unchecked_Access);
      STC.Suspend_Until_True (N.Trigger);
      W.Remove (N'Unchecked_Access);
   end Wait;

   procedure Broadcast (W : in out Wait_List) is
   begin
      W.Broadcast;
   end Broadcast;

   procedure Signal (W : in out Wait_List) is
   begin
      W.Signal;
   end Signal;
end Linted.Wait_Lists;
