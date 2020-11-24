package Complex_Abstract_State
  with Abstract_State => (A,
                          B,
                          (C with External => (Async_Writers,
                                               Effective_Reads => False)))
                          --  Three abstract state names are declared A, B & C.
                          --  A and B are internal abstract states.
                          --  C is specified as external state which is an external input.
is
   procedure Init;
end Complex_Abstract_State;
