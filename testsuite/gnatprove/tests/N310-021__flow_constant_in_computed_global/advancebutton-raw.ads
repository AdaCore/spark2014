-- Raw Advance Button Boundary Package
-- boundary package providing raw access to the advance switch
private package AdvanceButton.Raw
is
   procedure Read (Pressed : out Boolean);
   -- Pressed is True if the advance button is down.

end AdvanceButton.Raw;
