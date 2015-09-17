package Signals.Transient_Signals is

   protected type Transient_Signal is new Signal_Sender and
        Signal_Waiter with
      overriding procedure Send;
      overriding entry Wait;
   private
      Arrived : Boolean := False;
   end Transient_Signal;

   --type Transient_Signal_Access is access all Transient_Signal;

   protected type Pulse is new Signal_Sender and Signal_Waiter with
      overriding procedure Send;
      overriding entry Wait;
   private
      Arrived : Boolean := False;
   end Pulse;

   --type Pulse_Signal_Access is access all Pulse;

end Signals.Transient_Signals;
