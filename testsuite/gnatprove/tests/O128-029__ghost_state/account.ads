package Account with
  SPARK_Mode,
  Abstract_State => (State, Prev_State => Ghost)
is
   procedure Add_To_Total (Incr : in Integer) with
     Global => (In_Out => State);

end Account;
