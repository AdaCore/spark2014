package body Initial_Condition_Illegal_3
  with SPARK_Mode
is
   procedure Init is
   begin
      Var := 1;
   end Init;
begin
   Init;  --  Var is now set to 1. That makes
          --  the Initial_Condition False.
end Initial_Condition_Illegal_3;
