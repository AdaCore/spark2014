--  An example from "Concurrent and Real-Time Programming in Ada", Alan Burns
--  and Andy Wellings, CUP, 2007; section 10.3.

package Signals is

   type Sender is protected interface;

   procedure Send (S : in out Sender) is abstract;

   type Waiter is protected interface;

   procedure Wait (R : in out Waiter) is abstract;

   protected type Transient_Signal is new Sender and Waiter with
      overriding procedure Send;
      overriding entry Wait;
   private
      Arrived : Boolean := False;
   end Transient_Signal;

end Signals;
