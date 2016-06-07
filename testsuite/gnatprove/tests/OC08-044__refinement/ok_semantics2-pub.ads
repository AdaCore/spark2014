package OK_Semantics2.Pub with
  SPARK_Mode
is
   function Check return Boolean with
     Depends => (Check'Result => (State1, State2, State3));

   procedure Create with
     Depends => ((State1, State2, State3) => null);

   procedure Update with
     Depends => ((State1, State2, State3) =>+ null);

end OK_Semantics2.Pub;
