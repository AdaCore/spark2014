package Switch
with
   Abstract_State => (Volatile => (Input => State));
is

   type Reading is (on, off, unknown);

   function ReadValue return Reading;
   with
      Global => (Input => State);

end Switch;