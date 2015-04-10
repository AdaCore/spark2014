-- This is the private child of AdvanceButton from the Heating Controller Example.
-- The abstraction representing the external advance button input (Inputs) is
-- a constituent of the state of the parent's state abstraction.
-- I have chosen one possible way of indicating that the state abstraction
-- represents a volatile input but the purpose of this case study is not to
-- consider external inputs and outputs but to demonstrate data abstraction
-- using private children.
-- I will provide another case study with external inputs and outputs later.
private package AdvanceButton.Raw
with
  Abstract_State => (Inputs => (Volatile => Input))
is

   procedure Read (Pressed : out Boolean)
   with
     Global => (Input => Inputs),
     Depends => (Pressed => Inputs);
   --
   -- Pressed is TRUE if the advance button is down.

end AdvanceButton.Raw;
