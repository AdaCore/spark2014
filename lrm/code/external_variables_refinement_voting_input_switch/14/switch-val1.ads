private package Switch.Val1
   with Abstract_State => ((State with Volatile, Input))
is
   function Read return Switch.Reading
      with Global => (Input => State);
end Switch.Val1;
