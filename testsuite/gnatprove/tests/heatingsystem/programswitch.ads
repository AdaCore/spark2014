package ProgramSwitch
  with Abstract_State => (Inputs with External => Async_Writers)
is
   type Positions is (auto, clock, on1, off1, on2, off2);

   procedure Read (Value : out Positions)
     with Global  => Inputs,
          Depends => (Value => Inputs);
   -- Reads the position of the program switch.

end ProgramSwitch;
