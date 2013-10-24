private package Switch.Val2
  with Abstract_State => (State with External, Input_Only,
                                     Part_Of => Switch.State)
is
   function Read return Switch.Reading
     with Global => (Input => State);
end Switch.Val2;
