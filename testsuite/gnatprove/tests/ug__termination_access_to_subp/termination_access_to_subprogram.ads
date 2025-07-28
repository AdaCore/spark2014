package Termination_Access_To_Subprogram with SPARK_Mode is

   type Proc_Access is access procedure;
   type Func_Access is access function return Boolean;

   procedure P with Always_Terminates;
   function No_Call_Via_Access return Boolean;
   function Call_Via_Access return Boolean;

   procedure P_Term with Always_Terminates;

end Termination_Access_To_Subprogram;
