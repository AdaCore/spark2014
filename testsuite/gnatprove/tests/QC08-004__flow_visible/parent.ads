package Parent with Abstract_State => State is
   function Read return Integer with Global => (Input  => State);

   procedure Init               with Global => (Output => State);
   --  This procedure is only to silence a warning that State
   --  can't be initialized.
end;
