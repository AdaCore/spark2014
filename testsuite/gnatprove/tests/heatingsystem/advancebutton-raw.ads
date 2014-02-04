-- Raw Advance Button Boundary Package
-- boundary package providing raw access to the advance switch
private package AdvanceButton.Raw
  with Abstract_State => (Inputs with External => Async_Writers,
                                      Part_Of  => AdvanceButton.State)
is
   procedure Read (Pressed : out Boolean)
     with Global  => (In_Out => Inputs),
          Depends => ((Pressed,
                       Inputs) => Inputs);
   -- Pressed is True if the advance button is down.

end AdvanceButton.Raw;
