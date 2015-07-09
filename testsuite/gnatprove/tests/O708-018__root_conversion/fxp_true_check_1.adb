with Common; use Common;

procedure Fxp_True_Check_1 is
   MD : My_Duration := 0.0;
   MS : My_Subduration := 0.0;
begin
   pragma Assert (Duration (MD) >= 0.0);
   pragma Assert (Duration (MS) >= 0.0);
   pragma Assert (Duration (MD) < 1.0);
   pragma Assert (Duration (MS) < 1.0);
end;
