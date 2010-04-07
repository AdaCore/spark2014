with Time_Types;
package Timers is

   type Timer_Id is (TIMER_EVT_ETHARPTMR,
                     TIMER_EVT_TCPFASTTMR,
                     TIMER_EVT_TCPSLOWTMR,
                     TIMER_EVT_IPREASSTMR);

   procedure Initialize;
   procedure Set_Interval (TID : Timer_Id; Interval : Time_Types.Interval);
   function Timer_Fired (Now : Time_Types.Time; TID : Timer_Id) return Boolean;

   function Next_Deadline return Time_Types.Time;

end Timers;
