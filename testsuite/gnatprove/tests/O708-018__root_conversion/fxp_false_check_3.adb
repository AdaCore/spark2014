with Common; use Common;

procedure Fxp_False_Check_3 is
   M : Duration := Duration'Last;
begin
   pragma Assert (My_Subduration (My_Duration (M)) >= 0.0);
end;
