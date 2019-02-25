package body P is
   protected body PT is
      entry E when X is
         package Q with Initial_Condition => X is --@INITIAL_CONDITION:PASS
         end Q;
      begin
         declare
            package Q with Initial_Condition => X is
               --  ??? this should have @ INITIAL_CONDITION:PASS
            end Q;
         begin
            null;
         end;
         X := False;
         declare
            package Q with Initial_Condition => X is --@INITIAL_CONDITION:FAIL
            end Q;
         begin
            null;
         end;
      end E;
   end PT;
end P;
