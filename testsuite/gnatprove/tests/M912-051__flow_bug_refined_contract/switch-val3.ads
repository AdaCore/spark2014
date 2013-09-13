private package Switch.Val3
with SPARK_Mode, Abstract_State => (State with Part_Of => Switch.State)
is
   procedure Read (Value : out Switch.Reading)
   with Global  => State,
        Depends => (Value => State);

end Switch.Val3;
