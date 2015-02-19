package Account
  with SPARK_Mode,
       Abstract_State => (State, (Prev_State with Ghost))
is
   procedure Add_To_Total (Incr : in Integer)
     with Global => (In_Out => State,
                     Output => Prev_State);
end Account;
