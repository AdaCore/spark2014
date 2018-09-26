procedure My_Loop is
   Loop_Cond : Boolean := True;
begin
   while Loop_Cond loop
      Loop_Cond := False;
      pragma Loop_Invariant (True);
      pragma Assert (Loop_Cond); --@ASSERT:FAIL
   end loop;
end My_Loop;
