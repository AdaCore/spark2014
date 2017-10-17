with Call_Assign; use Call_Assign;
with Assign, Cond_Assign, Self_Assign;
procedure Bad_Call_Assign (X : in out Integer; C : in Choice) is
begin
   case C is
      when Simple =>
	 Assign (X, Integer'Last);
      when Conditional =>
	 Cond_Assign (X, Integer'Last, True);
      when Self =>
	 X := Integer'Last;
	 Self_Assign (X);
   end case;
end Bad_Call_Assign;
