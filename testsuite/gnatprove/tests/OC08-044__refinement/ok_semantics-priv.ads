private package OK_Semantics.Priv with
  SPARK_Mode,
  Abstract_State => (State with Part_Of => State3)
is
   function Check return Boolean with
     Global => (Input => (State1, State2, State3));

   procedure Create with
     Global => (Output => (State1, State2, State3));

   procedure Update with
     Global => (In_Out => (State1, State2, State3));

   YY : Integer := 0 with Part_Of => State2;

private
   ZZ : Integer := 0 with Part_Of => State;

end OK_Semantics.Priv;
