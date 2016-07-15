package Term with SPARK_Mode is
   function Loop_Except_On_Zero (X : Natural) return Natural with
     Post => (if X = 0 then Loop_Except_On_Zero'Result = 0 else False);

   procedure Do_Not_Loop (X : in out Natural) with
     Post => False;  --@ASSERT:FAIL
end Term;
