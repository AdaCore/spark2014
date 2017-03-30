with Socket;

package body Tracker_Interface is

   procedure Close is
   begin
      Socket.Cancel (Rec, Arr);
   end Close;

end Tracker_Interface;
