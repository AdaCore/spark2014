with Socket;

package Tracker_Interface is

   Rec : Socket.Selector_Rec with Async_Writers;
   Arr : Socket.Selector_Arr (1 .. 3) with Async_Writers;

   procedure Close with Global => (Input => (Rec, Arr));

end Tracker_Interface;
