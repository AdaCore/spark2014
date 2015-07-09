with Common; use Common;

procedure Fxp_True_Check_3a is
   MD : My_Duration := 0.0;
begin
   pragma Assert (My_Duration (Duration (MD)) = MD);
end;
