package External is
   type NvU32 is mod 2**32;
   function Get_Value return NvU32;
   procedure Error_Detected with No_Return;
   procedure Execute_Step_1;
   procedure Execute_Step_2;
   procedure Execute_Step_N;
end External;
