package Stack_ASM
  with Abstract_State => State
is



  function Is_Empty return Boolean
    with Global => State;

  function Top return Integer
    with Global => State,
         Pre    => not Is_Empty;

  procedure Push (V : Integer)
    with Global => (In_Out => State),
         Post   => not Is_Empty;

  procedure Clear
    with Global => (Output => State),
         Post   => Is_Empty;

  procedure Partial_Update
    with Global => (In_Out => State),
         Post   => Is_Empty;

end Stack_ASM;
