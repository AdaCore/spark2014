with Common; use Common;

procedure Fxp_True_Check_3b is
   MS : My_Subduration := 0.0;
begin
   pragma Assert (My_Subduration (Duration (MS)) = MS);
end;
