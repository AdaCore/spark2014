package PO_T5
  with Abstract_State => (State with Synchronous)
is
   --  TU: 6. A constituent of a synchronized state abstraction shall be a
   --  synchronized object or a synchronized state abstraction.

   procedure Does_Nothing;
end PO_T5;
