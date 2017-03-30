package Socket is

   type Selector_Rec is
      record
         Dummy : Integer;
      end record with Volatile;

   type Selector_Arr is array (Positive range <>) of Boolean with Volatile;

   procedure Cancel (The_Selector_Rec : Selector_Rec;
                     The_Selector_Arr : Selector_Arr);

end Socket;
