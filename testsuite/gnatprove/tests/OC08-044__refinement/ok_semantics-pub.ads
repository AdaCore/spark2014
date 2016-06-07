package OK_Semantics.Pub with
  SPARK_Mode
is
   function Check return Boolean with
     Global => (Input => (State1, State2, State3));

   procedure Create with
     Global => (Output => (State1, State2, State3));

   procedure Update with
     Global => (In_Out => (State1, State2, State3));

end OK_Semantics.Pub;
