with Socket;

package Tracker_Interface is

   Selector : Socket.Selector_Type with Async_Writers;

   procedure Close with Global => (Input => Selector);

end Tracker_Interface;
