with Socket;

package Tracker_Interface is

   Selector : Socket.Selector_Type with Async_Writers;

   procedure Close with Global => (In_Out => Selector);

end Tracker_Interface;
