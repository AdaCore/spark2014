package ProgramSwitch
is
   type Positions is (auto, clock, on1, off1, on2, off2);

   procedure Read (Value : out Positions);
   -- Reads the position of the program switch.

end ProgramSwitch;
