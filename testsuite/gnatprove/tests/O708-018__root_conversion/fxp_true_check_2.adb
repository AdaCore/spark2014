with Common; use Common;

procedure Fxp_True_Check_2 is
   MD : My_Duration;
   MS : My_Subduration := 0.0;
begin
   MD := 10.0;
   MS := My_Subduration(MD);
end;
