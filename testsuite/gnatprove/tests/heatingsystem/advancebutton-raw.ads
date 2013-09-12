
-- Raw Advance Button Boundary Package
-- boundary package providing raw access to the advance switch
private package AdvanceButton.Raw
--# own in Inputs;
is pragma SPARK_Mode (On);
   procedure Read (Pressed : out Boolean);
   --# global  in Inputs;
   --# derives Pressed from Inputs;
   --
   -- Pressed is True if the advance button is down.

end AdvanceButton.Raw;
