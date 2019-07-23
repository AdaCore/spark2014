with Ada.Synchronous_Task_Control; use Ada.Synchronous_Task_Control;

package P is
   pragma Elaborate_Body;
   SO : Suspension_Object;
   procedure Safe (S1, S2 : in out Suspension_Object);
   procedure Also_Safe (S1 : in out Suspension_Object);
end;
