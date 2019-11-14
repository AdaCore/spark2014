package sPIN
with
   Abstract_State => (Internal_State, (External_State with External)),
   Initializes => Internal_State
is

   type State_Type is record
      Current : Boolean;
   end record;

   function State_Invariant (S : State_Type) return Boolean
   with
      Ghost;

   procedure Initialize
      (State : out State_Type);

   procedure Display
      (State : in out State_Type);

end sPIN;
