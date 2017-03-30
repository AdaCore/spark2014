package Socket is

   type Selector_Type is
      record
         Dummy : Integer;
      end record with Volatile;

   procedure Cancel (The_Selector : Selector_Type);

end Socket;
