with Common; use Common;

procedure Fxp_False_Check_1b is
   MD : My_Duration := 0.0;
   MS : My_Subduration := 0.0;
begin
   pragma Assert (Duration (MD) < 0.0 or Duration (MS) < 0.0);
end;
