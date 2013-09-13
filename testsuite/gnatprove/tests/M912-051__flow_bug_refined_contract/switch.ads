package Switch
with SPARK_Mode, Abstract_State => State
is
   type Reading is (on, off, unknown);

   procedure ReadValue (Value : out Reading)
   with Global => State,
        Depends => (Value => State);

end Switch;
