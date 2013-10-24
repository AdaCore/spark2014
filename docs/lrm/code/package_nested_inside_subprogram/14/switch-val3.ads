private package Switch.Val3
  with Abstract_State => (Volatile => (Input => State))
is
   function Read return Switch.Reading
     with Global => (Input => State);
end Switch.Val3;
