--  An example from "Concurrent and Real-Time Programming in Ada", Alan Burns
--  and Andy Wellings, CUP, 2007; section 10.3 (adapted to SPARK).

package Signals is

   type Signal_Sender is protected interface;
   procedure Send(S : in out Signal_Sender) is abstract;
   --type Any_Signal_Sender is access all Signal_Sender'Class;

   type Signal_Waiter is protected interface;
   procedure Wait(S : in out Signal_Waiter) is abstract;
   --type Any_Signal_Waiter is access all Signal_Waiter'Class;

end Signals;
