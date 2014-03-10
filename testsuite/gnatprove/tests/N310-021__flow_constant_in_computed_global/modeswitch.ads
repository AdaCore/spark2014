package ModeSwitch
is
   type Modes is (off, cont, timed);

   procedure Read (Value : out Modes);
   -- Reads the position of the mode switch.

end ModeSwitch;
