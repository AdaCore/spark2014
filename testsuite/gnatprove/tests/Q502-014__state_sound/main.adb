pragma SPARK_Mode;

with State; use State;

procedure Main
  with Post => False --  @POSTCONDITION:FAIL
is
begin
   Set (0);
   Set (1);
end Main;
