private package Switch.Val2
with
   Abstract_State => (Volatile => (Input => State));
is
   function Read return Switch.Reading;
   with
      Global => (Input => State);

end Switch.Val2;