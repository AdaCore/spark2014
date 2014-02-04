package ModeSwitch
  with Abstract_State => (Inputs with External => Async_Writers)
is
   type Modes is (off, cont, timed);

   function PF_Read return Modes
     with Global => Inputs;

   procedure Read (Value : out Modes)
     with Global  => (In_Out => Inputs),
          Depends => ((Inputs,
                       Value) => Inputs),
          Post    => Value = PF_Read;
   -- Reads the position of the mode switch.

end ModeSwitch;
