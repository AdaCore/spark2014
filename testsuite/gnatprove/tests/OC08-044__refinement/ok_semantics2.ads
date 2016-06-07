package OK_Semantics2 with
  SPARK_Mode,
  Abstract_State => (State1, State2, State3)
is

private
   X : Integer := 0 with Part_Of => State1;
   Y : Integer := 0 with Part_Of => State2;
   Z : Integer := 0 with Part_Of => State3;

   function Check return Boolean with
     Depends => (Check'Result => (State1, State2, State3));

   procedure Create with
     Depends => ((State1, State2, State3) => null);

   procedure Update with
     Depends => ((State1, State2, State3) =>+ null);

end OK_Semantics2;
