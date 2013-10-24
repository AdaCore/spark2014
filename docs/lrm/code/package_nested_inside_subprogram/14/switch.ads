package Switch
  with Abstract_State => (State with External, Input_Only)
is
   type Reading is (on, off, unknown);

   function ReadValue return Reading
     with Global => (Input => State);
end Switch;
