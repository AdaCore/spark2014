
  -- boundary package providing raw access to the advance switch
  private package AdvanceButton.Raw
  --# own in Inputs;
  is

     procedure Read (Pressed : out Boolean);
    --# global  in Inputs;
    --# derives Pressed from Inputs;
    --
    -- Pressed is TRUE if the advance button is down.

  end AdvanceButton.Raw;
