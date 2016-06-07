private package OK_Semantics2.Priv with
  SPARK_Mode,
  Abstract_State => (State with Part_Of => State3)
is
   function Check return Boolean with
     Depends => (Check'Result => (State1, State2, State3));

   procedure Create with
     Depends => ((State1, State2, State3) => null);

   procedure Update with
     Depends => ((State1, State2, State3) =>+ null);

   YY : Integer := 0 with Part_Of => State2;

private
   ZZ : Integer := 0 with Part_Of => State;

end OK_Semantics2.Priv;
