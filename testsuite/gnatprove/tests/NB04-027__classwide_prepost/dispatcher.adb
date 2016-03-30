with Object; use Object;

procedure Dispatcher (X : in out T'Class) is
begin
   if X.B then
      X.Do_Stuff;  --  @PRECONDITION:FAIL
   end if;
end Dispatcher;
