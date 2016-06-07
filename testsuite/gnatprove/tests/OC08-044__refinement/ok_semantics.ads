package OK_Semantics with
  SPARK_Mode,
  Abstract_State => (State1, State2, State3)
is

private
   X : Integer := 0 with Part_Of => State1;
   Y : Integer := 0 with Part_Of => State2;
   Z : Integer := 0 with Part_Of => State3;

   function Check return Boolean with
     Global => (Input => (State1, State2, State3));

   procedure Create with
     Global => (Output => (State1, State2, State3));

   procedure Update with
     Global => (In_Out => (State1, State2, State3));

end OK_Semantics;
