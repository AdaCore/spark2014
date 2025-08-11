package body Termination_Access_To_Subprogram with SPARK_Mode is

   procedure P is null;

   function No_Call_Via_Access return Boolean is (True);

   function Call_Via_Access return Boolean is
      No_Call_Acc : Func_Access := No_Call_Via_Access'Access;
   begin
      return No_Call_Acc.all;
   end Call_Via_Access;

   procedure P_Term is
      P_Acc       : Proc_Access := P'Access;                  -- No check
      No_Call_Acc : Func_Access := No_Call_Via_Access'Access; -- No check
      Call_Acc    : Func_Access := Call_Via_Access'Access;    -- Check

      B : Boolean;
   begin
      P_Acc.all;                                              -- Check
      B := No_Call_Acc.all;
      B := Call_Acc.all;
   end P_Term;

end Termination_Access_To_Subprogram;
