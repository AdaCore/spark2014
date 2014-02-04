package ModeSwitch
  with Abstract_State => (Inputs with External => Async_Writers)
is
   type Modes is (off, cont, timed);

   procedure Read (Value : out Modes)
     with Global  => Inputs,
          Depends => (Value => Inputs);
   -- Reads the position of the mode switch.

end ModeSwitch;
